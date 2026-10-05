package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;
import edu.uva.liftlab.graphchecker.runtime.FieldAccess.MissingValue;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.ExpressionWalk;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import java.lang.reflect.Field;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.declaredInstanceField;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.exactFieldSignature;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.freshPrimitiveBox;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.readExactField;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.resolveFieldPathLeafOwner;
import static edu.uva.liftlab.graphchecker.runtime.ModelValues.isPrimitiveBox;
import static edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * Root minting (SYMBOL-SCOPE §4): where a root's value comes from, at every
 * cell a plan can declare.
 *
 * <p>Six mint shapes (root argument, helper argument or local, exact
 * {@code getstatic}, heap field, receiver field, configured source), one
 * rule: the VM is the authority.  A propagated expression is kept
 * ({@link #retainPropagatedInput}), a container keeps its own expression
 * ({@link #declaredContainerCell}), a cut port is never minted on
 * ({@link #observeCutPortWithoutMinting}); only the rest becomes a symbol.</p>
 *
 * <p>ONE PLACE DECIDES A MINT'S VALUE: {@link #focusedRootValue}, on the
 * occurrence the RECORDING minted at.  Woven hook names stay in
 * {@link ConcolicRegionRuntime} as delegates.</p>
 */
final class RootMint {
    /**
     * The clock roots each occurrence has read, as "owner address|root id":
     * a root is one clock SITE, and an occurrence's root is that site's
     * first reading there ({@link #materializePrimitiveValue}).
     */
    private static final Set<String> CLOCK_READINGS =
            ConcurrentHashMap.newKeySet();
    /**
     * The value each configuration root's symbol stands for in this JVM:
     * its first mint's.  The symbol is the key's, one per JVM (SYMBOL-SCOPE
     * §4.3), so it holds ONE value ({@link #configurationAgrees}).
     */
    private static final Map<String, String> CONFIGURATIONS =
            new ConcurrentHashMap<>();

    private RootMint() {
    }

    static void resetForTests() {
        CLOCK_READINGS.clear();
        CONFIGURATIONS.clear();
        NodeClocks.reset();
    }

    /**
     * Whether a mint of configuration {@code rootId} that runs at {@code
     * value} may carry the root's symbol: the first mint of the root in this
     * JVM fixes the value its symbol stands for, and a later mint at another
     * value -- another default of an unset key, another node's
     * configuration -- would state two values for one symbol, which a
     * witness could plant one perturbation for.  That read is read
     * concretely, named.
     */
    static boolean configurationAgrees(String rootId, String value,
                                       String where) {
        String standing = CONFIGURATIONS.putIfAbsent(safe(rootId),
                safe(value));
        if (standing == null || standing.equals(safe(value))) return true;
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                safe(rootId), "the configuration read at " + safe(where)
                        + " ran at " + safe(value) + " where the root's"
                        + " symbol stands for " + standing + " in this JVM"
                        + " (another default, view or node's"
                        + " configuration), so it is read concretely and no"
                        + " row states a mint of it");
        return false;
    }

    /** Called once per Java argument right after region entry. */
    static void symbolizeArgument(long token, int argumentIndex,
                                  Object value) {
        ActiveRegion active = ConcolicRegionRuntime.ownerRegion(token);
        if (active == null) {
            return;
        }
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.atArgument(argumentIndex)) continue;
            if (value == null) {
                if ("ARGUMENT".equals(action.location)
                        && action.declaresArrayInput(
                        Collections.<String>emptyList())) {
                    symbolize(active, action, null, engine());
                }
                continue;
            }
            if ("ARGUMENT_FIELD_PATH".equals(action.location)) {
                for (List<String> path : action.fieldPaths) {
                    symbolizeFieldPath(active, action, value, path, engine());
                }
            } else {
                symbolize(active, action, value, engine());
            }
        }
    }

    /** Symbolizes one scheduler-selected helper-method argument in-region. */
    static void symbolizeMethodArgument(String method, int argumentIndex,
                                        Object value) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
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
                continue;
            }
            symbolize(active, action, value, engine());
        }
    }

    /**
     * Mints the declared root argument before Java control flow consumes it;
     * Soot writes the result back to the parameter local.  Only a primitive
     * becomes a symbol; everything else passes through.
     */
    static Object materializeArgument(long token, int argumentIndex,
                                      Object boxedOrReference) {
        ActiveRegion active = ConcolicRegionRuntime.ownerRegion(token);
        if (active == null) return boxedOrReference;
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.atArgument(argumentIndex)) continue;
            if (boxedOrReference != null
                    && isPrimitiveBox(boxedOrReference)) {
                return materializePrimitiveValue(active, action,
                        boxedOrReference, null);
            }
        }
        return boxedOrReference;
    }

    /** Mints a declared live-in at an exact in-region helper parameter. */
    static Object materializeMethodArgument(String method, int argumentIndex,
                                            Object boxedOrReference) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
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
            return boxedOrReference;
        }
        return boxedOrReference;
    }

    /** Materializes a reference-valued live-in at its defining Jimple local. */
    static Object materializeReference(String method, int unitIndex,
                                              String local, Object value) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active == null) {
            return value;
        }
        int occurrence = active.materializationOccurrences.local(
                method, unitIndex, local);
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesLocal(method, unitIndex, local)
                    || !action.acceptsOccurrence(occurrence)) {
                continue;
            }
            if (!active.materialized.add(action.symbol)) {
                continue;
            }
            if (isPrimitiveBox(value)) {
                return materializePrimitiveValue(active, action, value, null);
            }
            if (value != null || action.declaresArrayInput(
                    Collections.<String>emptyList())) {
                symbolize(active, action, value, engine());
            }
            return value;
        }
        return value;
    }

    /**
     * Materializes a primitive live-in as a fresh box, which Soot unboxes
     * back into the local so the symbolic expression reaches the branch.
     */
    static Object materializePrimitive(String method, int unitIndex,
                                              String local,
                                              Object boxedValue) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active == null || boxedValue == null) {
            return boxedValue;
        }
        int occurrence = active.materializationOccurrences.local(
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

    /** Materializes the primitive read by one exact {@code getstatic}. */
    static Object materializeStaticPrimitiveField(
            String method, int unitIndex, String fieldSignature,
            String fieldName, Object boxedValue) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
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
            return boxedValue;
        }
        return materializePrimitiveValue(active, selected, boxedValue,
                logicalPath);
    }

    static void materializeField(String method, int unitIndex,
                                        Object owner, String fieldSignature,
                                        String fieldName) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active == null || owner == null) return;
        int occurrence = active.materializationOccurrences.field(
                method, unitIndex);
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesField(method, unitIndex, owner, fieldSignature,
                    fieldName)
                    || !action.acceptsDirectFieldOccurrence(occurrence)) {
                continue;
            }
            Object leafOwner = action.leafOwner(owner);
            if (leafOwner == null || leafOwner == MissingValue.INSTANCE) {
                continue;
            }
            if (!active.materialized.add(action.symbol)) continue;
            Object value = MissingValue.INSTANCE;
            try {
                ConcolicVmBroker api = engine();
                Field exactField = declaredInstanceField(leafOwner,
                        action.exactLeafFieldSignature());
                if (exactField == null) {
                    continue;
                }
                String leafFieldSignature = exactFieldSignature(exactField);
                value = exactField.get(leafOwner);
                JsonElement carried;
                try {
                    carried = cellExpression(api, leafOwner,
                            exactField.getDeclaringClass().getName(),
                            exactField.getName(), javaTypeDescriptor(
                                    exactField.getType().getTypeName()),
                            value);
                } catch (ConcolicRegionRuntime.PropagatedExpressionImportFailure unreadable) {
                    continue;
                } catch (Throwable unsymbolized) {
                    carried = null;
                }
                // Asked before any write or mint: a propagated value wins.
                if (retainPropagatedInput(active, action, value, carried,
                        action.symbol, action.fieldPath,
                        leafFieldSignature)) {
                    continue;
                }
                if (declaredContainerCell(value)) {
                    continue;
                }
                MintedLeaf minted = mintExactFieldLeaf(active, action,
                        api, leafOwner, leafFieldSignature, action.symbol,
                        value);
                if (minted == null) {
                    readConcretely(active, action.symbol, value);
                    continue;
                }
                active.recordManualSymbolization(action, action.symbol,
                        action.fieldPath, leafFieldSignature,
                        minted.expression, true, false,
                        minted.recordedValue, 0L);
            } catch (Throwable throwable) {
                readConcretely(active, action.symbol, value);
                // Stated, never swallowed: a failed mint and an undeclared
                // cell otherwise read identically from the corpus.
                RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        firstNonBlank(action.symbol, action.actionDigest),
                        "the declared heap-field input at "
                                + SiteId.render(method, unitIndex)
                                + " was not minted, so the region reads it"
                                + " concretely and no row states a value"
                                + " for it: " + ConcolicRegionRuntime.rootCause(throwable));
            }
        }
    }

    /**
     * One read of one declared mint site.
     *
     * <p>A configured source is ONE symbol: every read of its site, in any
     * occurrence or session, binds to it.  Trap: putting the read number in
     * the label splits one marker into free variables a flip moves only
     * one of.</p>
     */
    static final class SourceSiteEntry {
        private final ConfiguredSourcePhaseContract.Occurrence phase;
        final String siteId;
        SourceSiteEntry(
                ConfiguredSourcePhaseContract.Occurrence phase,
                String siteId) {
            this.phase = phase;
            this.siteId = safe(siteId);
        }

        String phaseId() {
            return phase.phaseId();
        }

        /** HOOK: a tree's hook mints here; CONFIG: the engine's read. */
        RootCategory category() {
            return phase.category();
        }

        /** A CONFIG site's static domain bound, or {@code ""}. */
        String domainMin() {
            return phase.domainMin();
        }

        String domainMax() {
            return phase.domainMax();
        }
    }

    /**
     * THE ACTIVATION THAT OWNS THIS MINT, or {@code null} when no admitted
     * activation of this session does.
     *
     * <p>Asked by every mint before it symbolizes: a symbol is answerable
     * only through the {@link edu.uva.liftlab.graphchecker.contract
     * .RootMintRow} its activation publishes, so a mint is symbolized AND
     * rowed, or refused by name.  Resolved at the region that OWNS the root
     * ({@link ActiveRegion#rootOwner}).  No {@code d3Address} means not
     * admitted.</p>
     */
    static ActiveRegion mintOwner(ActiveRegion active, String rootId) {
        if (active == null || !RowRuntime.open()) return null;
        ActiveRegion owner = active.rootOwner(rootId);
        return owner.d3Address == null ? null : owner;
    }

    /**
     * Refuses one mint nothing admitted owns: the value stays concrete and
     * the session states MINT_UNATTRIBUTED.  BLOCKING when the obligation
     * assigns the root (the replay did not run what was asked), DIAGNOSTIC
     * otherwise.  The other branch publishes the mint row
     * ({@code RowPlaceholderMint#roots}); never a symbol without a row.
     */
    static boolean mintUnattributed(ActiveRegion active, String rootId,
                                    String context) {
        if (mintOwner(active, rootId) != null) return false;
        RowRuntime.gap(GapKind.MINT_UNATTRIBUTED,
                assignedByTheWave(rootId)
                        ? GapClass.BLOCKING
                        : GapClass.DIAGNOSTIC,
                firstNonBlank(safe(rootId), safe(context)),
                "no admitted activation of this session owns this mint ("
                        + safe(context) + "), so the declared root is read"
                        + " concretely and no symbol is minted for it; the"
                        + " read stands at no occurrence, so no reading of"
                        + " it guards the arms that rest on it");
        return true;
    }

    /** Whether the obligation this session runs assigns this root. */
    private static boolean assignedByTheWave(String rootId) {
        return !FocusedReplay.rootAssignment(safe(rootId)).isEmpty()
                || FocusedReplay.clockSkew(safe(rootId)) != null;
    }

    /**
     * Mints one symbol for one entry of a declared mint site, or states what
     * the read held where none was minted ({@link #readConcretely}): an
     * occurrence run concretely, a mint refused, unattributed or failed.  A
     * field that already carries a propagated expression keeps it, the row
     * says {@code reused}, and the root is derived here.
     *
     * <p>Called from outside this repository, by the workload's
     * {@code org.apache.hadoop.ipc.CausynthSymbolicSource}, and by the
     * engine's configuration read ({@link #configuration}).</p>
     */
    static boolean configuredSource(
            String sourceId, Object owner, String fieldSignature) {
        // No owner on this entry is not a gap.
        if (owner == null) return false;
        // A native reproduction writes the value its plant assigns; no
        // engine runs there.
        if (RecordingPlant.planting()) {
            RecordingPlant.hook(safe(sourceId), owner, safe(fieldSignature));
            return false;
        }
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (mintConfiguredSource(active, safe(sourceId), owner,
                safe(fieldSignature))) {
            return true;
        }
        ConcolicRegionRuntime.pauseObservation();
        try {
            readConcretely(active, safe(sourceId),
                    readExactField(owner, safe(fieldSignature)));
        } catch (Throwable ignored) {
            // Observation must never alter the workload's own outcome.
        } finally {
            ConcolicRegionRuntime.resumeObservation();
        }
        return false;
    }

    /** {@link #configuredSource}'s mint: whether a symbol was minted or
     *  reused. */
    private static boolean mintConfiguredSource(ActiveRegion active,
                                                String sourceId, Object owner,
                                                String fieldSignature) {
        // A region running concretely contributes literals, never a free
        // root; asked first, as it owns no mint to refuse.
        if (!ActiveRegion.mintsUnderSymbolicOccurrence(active, sourceId,
                fieldSignature)) {
            return false;
        }
        SourceSiteEntry entry = active.observeConfiguredSourceEntry(
                safe(sourceId), safe(fieldSignature));
        if (entry == null) return false;
        ConcolicRegionRuntime.pauseObservation();
        try {
            Field field = declaredInstanceField(owner, safe(fieldSignature));
            if (field == null || !field.getType().isPrimitive()) {
                return false;
            }
            // Before the VM is touched: no symbol without a row.
            if (mintUnattributed(active, safe(sourceId),
                    "configured source at " + entry.siteId)) {
                return false;
            }
            ConcolicVmBroker api = engine();
            String declaringClass = field.getDeclaringClass().getName();
            String descriptor = javaTypeDescriptor(
                    field.getType().getTypeName());
            // Did the value arrive with its own expression?  A VM with no
            // answer for an unsymbolized field is answering "no".
            JsonElement carried;
            try {
                carried = ConcolicRegionRuntime.engineExpression(api.fieldExpression(owner,
                        declaringClass, field.getName(), descriptor,
                        field.get(owner)));
            } catch (ConcolicRegionRuntime.PropagatedExpressionImportFailure unreadable) {
                return false;
            } catch (Throwable unsymbolized) {
                carried = null;
            }
            // #carriesInputAuthority's strict question (a configured source
            // is a declared primitive): a ReadFrom wrapper of constants is
            // not an expression of its own.
            boolean reused = VmExpressionIr.carriesSymbolicValue(carried);
            if (reused) RowRuntime.derivedRoot(sourceId);
            // What the region observed, read before the plant overwrites it;
            // a configuration's world value is already there (#configuration).
            String observed = ConcolicRegionRuntime.recordedScalar(
                    field.get(owner));
            if (!reused && entry.category() == RootCategory.CONFIG
                    && !configurationAgrees(safe(sourceId), observed,
                    entry.siteId)) {
                return false;
            }
            // The wave's value is written first: the app's Map re-key reads
            // it back through this same path.
            String planted = "";
            if (!reused && entry.category() != RootCategory.CONFIG) {
                planted = applyFocusedRootAssignment(active, safe(sourceId),
                        owner, safe(fieldSignature), descriptor);
            }
            // ONE SYMBOL PER DECLARED SOURCE: the label is the source's
            // alone, so a flip moves every read.  The row is still one per
            // READ.
            String symbol = ConfiguredSourcePhaseContract.engineLabel(
                    safe(sourceId));
            if (!reused) {
                api.symbolizeExactField(owner, exactFieldSignature(field),
                        declaring(symbol));
            }
            Object value = field.get(owner);
            JsonElement expression = ConcolicRegionRuntime.engineExpression(api.fieldExpression(
                    owner, declaringClass, field.getName(), descriptor,
                    value));
            if (!reused && mintRefused(expression, symbol,
                    jvmShared(api, owner), "the configured source field "
                            + safe(fieldSignature), safe(sourceId))) {
                return false;
            }
            active.pathRecordingStarted = true;
            // A mint that PLANTED states what it ran at, or the root is
            // stated twice and differently and Composer refuses the path.
            // A CLOCK states its reading: FlipQuery bounds the cell by it.
            String stated = !planted.isEmpty()
                    && FocusedReplay.clockSkew(safe(sourceId)) == null
                    ? planted : observed;
            active.recordConfiguredSourceMint(entry, safe(sourceId),
                    safe(fieldSignature), symbol, expression, reused,
                    stated);
            return true;
        } catch (Throwable failure) {
            // Never into the workload's own read; never silent.
            RowRuntime.gap(GapKind.UNSTATED_VALUE, assignedByTheWave(
                    safe(sourceId)) ? GapClass.BLOCKING : GapClass.DIAGNOSTIC,
                    safe(sourceId), "the configured source at "
                            + entry.siteId + " was not minted, so the region"
                            + " reads " + safe(fieldSignature) + " as it was"
                            + " and no row states a mint of it: "
                            + ConcolicRegionRuntime.rootCause(failure));
            return false;
        } finally {
            ConcolicRegionRuntime.resumeObservation();
        }
    }

    /**
     * States what a declared root held where this replay read it and minted
     * none ({@link RowRuntime#concreteReading}), at the occurrence a mint
     * there is addressed at ({@code ActiveRegion#mintOccurrence}), so a
     * reading and another session's mint of one occurrence compare.  A read
     * no addressed activation owns stands at no occurrence and states
     * nothing: its MINT_UNATTRIBUTED gap names it ({@link #mintUnattributed}).
     */
    private static void readConcretely(ActiveRegion active, String rootId,
                                       Object value) {
        if (active == null) return;
        String occurrence = active.rootOwner(rootId).address();
        if (occurrence.isEmpty()) return;
        RowRuntime.concreteReading(rootId, occurrence,
                ConcolicRegionRuntime.recordedScalar(value));
    }

    /**
     * The engine's configuration read, woven before the {@code getfield} of
     * a configuration field (SYMBOL-SCOPE §4.3).  A configuration belongs
     * to the world, not to an occurrence: the value an obligation assigns
     * it is written at every read of it, on every node, whatever occurrence
     * runs it; then the read mints as a configured source does, stating
     * what it read.  It never throws into the workload's read: a failure
     * is named, BLOCKING where the wave assigns the root.
     */
    static void configuration(String sourceId, Object owner,
                              String fieldSignature) {
        if (owner == null) return;
        try {
            String assigned = FocusedReplay.rootAssignment(safe(sourceId));
            if (!assigned.isEmpty()) {
                plantConfiguration(safe(sourceId), owner,
                        safe(fieldSignature), assigned);
            }
            configuredSource(sourceId, owner, fieldSignature);
        } catch (Throwable failure) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, assignedByTheWave(
                    safe(sourceId)) ? GapClass.BLOCKING : GapClass.DIAGNOSTIC,
                    safe(sourceId), "the configuration read of "
                            + safe(fieldSignature) + " failed, so the region"
                            + " reads the field as it was and no row states a"
                            + " mint of it: "
                            + ConcolicRegionRuntime.rootCause(failure));
        }
    }

    /** Writes a configuration's assigned value into the field one read of
     *  it loads, unless a mint of this replay stands there already (and
     *  holds it). */
    private static void plantConfiguration(String sourceId, Object owner,
                                           String fieldSignature,
                                           String value) {
        FocusedReplay.mintReached(sourceId);
        ConcolicRegionRuntime.pauseObservation();
        try {
            Field field = declaredInstanceField(owner, fieldSignature);
            if (field == null) return;
            String descriptor = javaTypeDescriptor(
                    field.getType().getTypeName());
            JsonElement carried;
            try {
                carried = ConcolicRegionRuntime.engineExpression(engine()
                        .fieldExpression(owner,
                                field.getDeclaringClass().getName(),
                                field.getName(), descriptor,
                                field.get(owner)));
            } catch (Throwable unsymbolized) {
                carried = null;
            }
            if (VmExpressionIr.carriesSymbolicValue(carried)) return;
            if (writeModeledField(owner, fieldSignature, descriptor, value)) {
                FocusedReplay.planted(sourceId);
                return;
            }
            RowRuntime.gap(GapKind.UNPRODUCIBLE_ANSWER, GapClass.BLOCKING,
                    sourceId, "the wave's assignment for this configuration"
                            + " could not be written into "
                            + fieldSignature);
        } catch (Throwable failure) {
            // A read of the workload's own field: never perturb it, and
            // never lose the plant silently.
            RowRuntime.gap(GapKind.UNPRODUCIBLE_ANSWER, GapClass.BLOCKING,
                    sourceId, "the wave's assignment for this configuration"
                            + " could not be written into " + fieldSignature
                            + ": " + ConcolicRegionRuntime.rootCause(failure));
        } finally {
            ConcolicRegionRuntime.resumeObservation();
        }
    }

    /**
     * The value the wave asks of this root at its mint, or {@code ""}.
     *
     * <p>The one decision for every mint, applied only on an occurrence of
     * the FOCUSED SET ({@code FocusedReplay#focused}); elsewhere it would
     * state what the obligation never asked.  A clock is a SKEW added to
     * {@code observed}, the instant this run read: every execution reads a
     * clock fresh, and pinning the recorded instant leaves paths unsat.</p>
     */
    static String focusedRootValue(ActiveRegion active,
                                           String rootId, Object observed) {
        FocusedReplay.mintReached(rootId);
        if (active == null) return "";
        // At the region that OWNS the mint, as the recording resolved it.
        ActiveRegion owner = active.rootOwner(rootId);
        if (owner.d3Address == null) return "";
        if (!FocusedReplay.focused(owner.d3Address)) {
            return "";
        }
        Long skew = FocusedReplay.clockSkew(rootId);
        if (skew == null) {
            return FocusedReplay.rootAssignment(rootId);
        }
        Long reading = readingOf(observed);
        if (reading == null) {
            RowRuntime.gap(GapKind.UNPRODUCIBLE_ANSWER,
                    GapClass.BLOCKING, rootId,
                    "the wave states a skew for this clock and the mint read"
                            + " no instant to add it to");
            return "";
        }
        return Long.toString(reading.longValue() + skew.longValue());
    }

    /** One integral reading, or null when the value is not one. */
    private static Long readingOf(Object value) {
        return value instanceof Number && !(value instanceof Float)
                && !(value instanceof Double)
                ? Long.valueOf(((Number) value).longValue()) : null;
    }

    /**
     * Writes that value into the declared field the mint stands on.
     *
     * @return the value written (the mint states it), or {@code ""}
     */
    private static String applyFocusedRootAssignment(
            ActiveRegion active, String sourceId, Object owner,
            String fieldSignature, String descriptor) {
        String value = focusedRootValue(active, sourceId,
                readExactField(owner, fieldSignature));
        if (value.isEmpty()) return "";
        if (!active.mintIsPlaceable(owner)) return "";
        if (writeModeledField(owner, fieldSignature, descriptor, value)) {
            // Filed only on a write: an unplaced one is ASSIGNMENT_UNPLANTED.
            FocusedReplay.planted(sourceId);
            return value;
        }
        RowRuntime.gap(GapKind.UNPRODUCIBLE_ANSWER,
                GapClass.BLOCKING, sourceId,
                "the wave's assignment for this root could not be"
                        + " written into " + fieldSignature);
        return "";
    }

    static void symbolizeReceiverFields(ActiveRegion active,
                                               RuntimeTask task,
                                               ConcolicVmBroker api) {
        for (SymbolizeAction action : task.symbolize) {
            // Nested heap fields are minted at the field-access hook.
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
        Object value = MissingValue.INSTANCE;
        try {
            String leafFieldSignature = action.exactLeafFieldSignature(
                    exactFieldPath);
            value = readExactField(owner, leafFieldSignature);
            DeclaredField field = FieldPathSpec.declaredField(
                    leafFieldSignature);
            if (field == null) {
                return;
            }
            JsonElement carried = cellExpression(api, owner, field.owner(),
                    field.name(), javaTypeDescriptor(field.type()), value);
            if (retainPropagatedInput(active, action, value, carried, symbol,
                    exactFieldPath, leafFieldSignature)) {
                return;
            }
            if (declaredContainerCell(value)) {
                return;
            }
            MintedLeaf minted = mintExactFieldLeaf(active, action, api,
                    owner, leafFieldSignature, symbol, value);
            if (minted == null) {
                readConcretely(active, action.symbol, value);
                return;
            }
            active.recordManualSymbolization(action, symbol, exactFieldPath,
                    leafFieldSignature, minted.expression, true, false,
                    minted.recordedValue, 0L);
        } catch (Throwable throwable) {
            readConcretely(active, action.symbol, value);
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, symbol,
                    "this declared field input was not minted, so the region"
                            + " reads it concretely and no row states a"
                            + " value for it: " + ConcolicRegionRuntime.rootCause(throwable));
        }
    }

    /**
     * Mints the scalar leaf of one exact field read: the expression the VM
     * then carries and the recorded value, or {@code null} when the leaf has
     * no resolvable declaration.
     *
     * <p>Shared by the receiver-field ({@link #symbolizeField}) and heap-field
     * ({@link #materializeField}) hooks, and where the wave's value reaches a
     * field mint ({@link #focusedRootValue}).</p>
     */
    private static MintedLeaf mintExactFieldLeaf(
            ActiveRegion active, SymbolizeAction action,
            ConcolicVmBroker api, Object owner, String leafFieldSignature,
            String symbol, Object value) throws Exception {
        DeclaredField field = FieldPathSpec.declaredField(leafFieldSignature);
        if (field == null) {
            return null;
        }
        if (mintUnattributed(active, action.symbol,
                "declared field input at " + leafFieldSignature)) {
            return null;
        }
        String descriptor = javaTypeDescriptor(field.type());
        String recorded = fieldMintRecordedValue(active, action, owner,
                leafFieldSignature, descriptor, value);
        // Re-read: after a plant the cell holds the wave's value, without
        // one it holds what was read, so no plant flag is needed.
        Object held = readExactField(owner, leafFieldSignature);
        if (held == MissingValue.INSTANCE) held = value;
        String label = declaring(manualMintLabel(symbol,
                active.activation.occurrenceId,
                JavaPrimitiveSmtSemantics.primitive(field.type())));
        api.symbolizeExactField(owner, leafFieldSignature, label);
        JsonElement expression = ConcolicRegionRuntime.engineExpression(
                api.fieldExpression(owner, field.owner(), field.name(),
                        descriptor, held));
        if (mintRefused(expression, label, jvmShared(api, owner),
                "the declared field " + leafFieldSignature, symbol)) {
            return null;
        }
        active.pathRecordingStarted = true;
        return new MintedLeaf(expression, recorded);
    }

    /** One field leaf's mint: what the VM carries, and what the row may say. */
    private static final class MintedLeaf {
        private final JsonElement expression;
        private final String recordedValue;

        private MintedLeaf(JsonElement expression, String recordedValue) {
            this.expression = expression;
            this.recordedValue = recordedValue;
        }
    }

    /**
     * Plants the wave's value at one field mint ({@link #focusedRootValue})
     * and returns what the mint OBSERVED there.
     *
     * <p>A mint row always states the observed value, even when a plant
     * follows: a root with no stated value has no centre for a relative
     * domain, so IMPORT refuses it (invariant 8).  The session's valuation is
     * stated by the FOCUS row only.</p>
     */
    static String fieldMintRecordedValue(
            ActiveRegion active, SymbolizeAction action, Object owner,
            String leafFieldSignature, String descriptor, Object value) {
        applyFocusedRootAssignment(active, action.symbol, owner,
                leafFieldSignature, descriptor);
        return ConcolicRegionRuntime.recordedScalar(value);
    }

    private static void symbolizeFieldPath(ActiveRegion active,
                                           SymbolizeAction action,
                                           Object root,
                                           List<String> path,
                                           ConcolicVmBroker api) {
        String label = FieldPathSpec.join(path);
        if (path == null || path.isEmpty() || label.isEmpty()) {
            return;
        }
        Object leafOwner = resolveFieldPathLeafOwner(root, path);
        if (leafOwner == null || leafOwner == MissingValue.INSTANCE) {
            return;
        }
        symbolizeField(active, action, leafOwner, label, path, api);
    }

    private static Object materializePrimitiveValue(
            ActiveRegion active, SymbolizeAction action, Object concrete,
            List<String> path) {
        // A configuration's root is its key's (SYMBOL-SCOPE §4.3), else the
        // input's own.
        boolean config = !action.configSource.isEmpty();
        String root = config ? action.configSource : action.symbol;
        FocusedReplay.mintReached(root);
        ConcolicVmBroker api = engine();
        List<String> exactPath = path == null
                ? Collections.<String>emptyList() : path;
        String fieldSignature = path == null ? ""
                : action.exactLeafFieldSignature(path);
        JsonElement carried;
        try {
            carried = primitiveBoxExpression(api, concrete);
        } catch (ConcolicRegionRuntime.PropagatedExpressionImportFailure unreadable) {
            return concrete;
        } catch (Throwable unsymbolized) {
            carried = null;
        }
        // A value carrying an expression was computed from a reading, which
        // ran at its clock already: kept whole, never moved again.
        if (retainPropagatedInput(active, action, concrete, carried,
                action.symbol, exactPath, fieldSignature)) {
            return concrete;
        }
        // No node owns it, so it is on no node's clock: the host's reading,
        // named MINT_UNATTRIBUTED.
        if (mintUnattributed(active, action.symbol,
                "declared primitive input at "
                        + firstNonBlank(fieldSignature, action.cell))) {
            return concrete;
        }
        // A clock reads its node's clock (NodeClocks): the host's reading
        // moved by the jump before it.
        ActiveRegion owner = active.rootOwner(action.symbol);
        String node = owner.d3Address.node().render();
        boolean clock = action.declaresWallClockRead()
                && readingOf(concrete) != null;
        Object ran = clock ? clockReading(node, action, concrete) : concrete;
        // The box minted here IS what the region reads back, so the plant
        // goes into it (#focusedRootValue); a configuration's is the world's,
        // whatever occurrence reads it.
        String assigned = config ? FocusedReplay.rootAssignment(root)
                : focusedRootValue(active, action.symbol, concrete);
        Object planted = ran;
        if (!assigned.isEmpty()) {
            Object modeled = ModelValues.coerce("", assigned,
                    concrete == null ? null : concrete.getClass());
            if (modeled == null
                    || modeled == ModelValues.UnsupportedReplayValue.INSTANCE) {
                RowRuntime.gap(GapKind.UNPRODUCIBLE_ANSWER,
                        GapClass.BLOCKING, action.symbol,
                        "the wave's value for this root could not be read as"
                                + " the type the mint reads");
                assigned = "";
            } else {
                planted = modeled;
            }
        }
        if (config) {
            // The key's one symbol holds one value in this JVM: a read at
            // another is read concretely (#configurationAgrees).  One read
            // twice in one occurrence is the box its first read minted, no
            // second root row (invariant 8).
            if (!configurationAgrees(root, ConcolicRegionRuntime
                    .recordedScalar(planted), firstNonBlank(action.siteId,
                    action.cell))) {
                return concrete;
            }
            Object read = active.configurationRead(root, action.symbol);
            if (read != null) return read;
        }
        // A clock site read again in the occurrence that read it (a loop's
        // bodies share one address) is a later instant of the same root at
        // the same place: its node's clock, concrete.  One symbol for both
        // would state two values for one source (IMPORT invariant 8).
        if (action.clock != null && !CLOCK_READINGS.add(owner.address()
                + "|" + action.symbol)) {
            return ran;
        }
        Object fresh = freshPrimitiveBox(planted);
        try {
            // A configuration is one symbol per key, in every occurrence and
            // session; any other input one per occurrence.
            api.symbolizeField(fresh, "value", declaring(config
                    ? ConfiguredSourcePhaseContract.engineLabel(root)
                    : manualMintLabel(action.symbol,
                    active.activation.occurrenceId, true)));
            active.pathRecordingStarted = true;
            JsonElement expression = primitiveBoxExpression(api, fresh);
            // What the region ran the root at: the box's value.  A clock
            // also states how far its node's clock ran off the host there,
            // the reading a skew is relative to (RootMintRow#hostReading).
            active.recordManualSymbolization(action, action.symbol,
                    exactPath, fieldSignature, expression, true, false,
                    ConcolicRegionRuntime.recordedScalar(planted),
                    clock ? clockSkew(node, action, concrete, planted,
                            !assigned.isEmpty()) : 0L);
            if (!assigned.isEmpty()) FocusedReplay.planted(root);
            if (config) active.configurationMinted(root, fresh);
            // The region takes a door fault: it ends the exchange in hand,
            // as a native plant's does (any other root names no marker).
            if (Boolean.TRUE.equals(fresh)) {
                Identity.doorFaulted(action.marker);
            }
            return fresh;
        } catch (Throwable throwable) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, assignedByTheWave(root)
                            ? GapClass.BLOCKING : GapClass.DIAGNOSTIC, root,
                    "the declared input at " + firstNonBlank(fieldSignature,
                            action.cell) + " was not minted, so the region"
                            + " reads it concretely and no row states a"
                            + " value for it: "
                            + ConcolicRegionRuntime.rootCause(throwable));
            return ran;
        }
    }

    /**
     * The value one declared clock reading runs at: its node's clock
     * ({@link NodeClocks}), the host's reading moved by the skew of the jump
     * before it in the recording's order.  The host's own box where there is
     * none; where the mint's type cannot hold the instant, the host's, named
     * BLOCKING.
     */
    static Object clockReading(String node, SymbolizeAction action,
                               Object host) {
        long skew = NodeClocks.skew(node, action.clock, action.eventSeq);
        if (skew == 0L) return host;
        long instant = readingOf(host).longValue() + skew;
        Object moved = ModelValues.coerce("", Long.toString(instant),
                host.getClass());
        if (moved == null
                || moved == ModelValues.UnsupportedReplayValue.INSTANCE) {
            RowRuntime.gap(GapKind.UNPRODUCIBLE_ANSWER, GapClass.BLOCKING,
                    action.symbol, "this clock reading runs on at instant "
                            + instant + ", which the type the mint reads "
                            + "cannot hold, so it reads the host's");
            return host;
        }
        return moved;
    }

    /**
     * How far a minted clock reading ran off the host's reading (the skew
     * its row states), filed as a jump of its node's clock where the wave
     * planted it: the clock runs on from there.  A reading the recording
     * states no event for, or whose clock states no source, is on no
     * clock's order, and the plant moves it alone (named).
     */
    static long clockSkew(String node, SymbolizeAction action,
                          Object host, Object ran, boolean planted) {
        long skew = readingOf(ran).longValue() - readingOf(host).longValue();
        if (planted && !NodeClocks.jump(node, action.clock, action.eventSeq,
                skew)) {
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    action.symbol, "this clock reading has no place on its "
                            + "node's clock (recorded event " + action.eventSeq
                            + ", clock " + action.clock + "), so the plant "
                            + "moves this reading alone");
        }
        return skew;
    }

    /** Exact expression stored in a Java primitive wrapper's value field. */
    private static JsonElement primitiveBoxExpression(
            ConcolicVmBroker api, Object boxed) throws Exception {
        if (boxed == null) return null;
        String descriptor = JavaPrimitiveBoxing.primitiveDescriptor(
                boxed.getClass().getName());
        if (descriptor.isEmpty()) return null;
        return ConcolicRegionRuntime.engineExpression(api.fieldExpression(boxed,
                boxed.getClass().getName(), "value", descriptor, boxed));
    }

    /**
     * Writes one value the wave stated into one exact field: the one place
     * a replay's own value reaches the workload's heap.
     */
    static boolean writeModeledField(Object owner, String fieldSignature,
                                     String valueType, String value) {
        Field field = declaredInstanceField(owner, fieldSignature);
        if (field == null) return false;
        try {
            Object modeled = ModelValues.coerce(valueType, value,
                    field.getType());
            if (modeled == ModelValues.UnsupportedReplayValue.INSTANCE) {
                return false;
            }
            field.set(owner, modeled);
            return true;
        } catch (Throwable ignored) {
            return false;
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
                    : ConcolicRegionRuntime.engineExpression(api.expression(value));
            if (retainPropagatedInput(active, action, value, carried,
                    action.symbol, Collections.<String>emptyList(), "")) {
                return;
            }
            if (declaredContainerCell(value)) {
                return;
            }
            if (mintUnattributed(active, action.symbol,
                    "declared input at " + action.cell)) {
                return;
            }
            String label = declaring(manualMintLabel(action.symbol,
                    active.activation.occurrenceId, isPrimitiveBox(value)));
            api.symbolize(value, label);
            JsonElement expression = value == null ? null
                    : ConcolicRegionRuntime.engineExpression(api.expression(value));
            if (value != null && mintRefused(expression, label,
                    jvmShared(api, value), "this declared input (a "
                            + value.getClass().getName() + ")",
                    firstNonBlank(action.symbol, action.actionDigest))) {
                readConcretely(active, action.symbol, value);
                return;
            }
            active.pathRecordingStarted = true;
            active.recordManualSymbolization(action, action.symbol,
                    Collections.<String>emptyList(), "", expression,
                    true, false, "", 0L);
        } catch (Throwable throwable) {
            readConcretely(active, action.symbol, value);
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    firstNonBlank(action.symbol, action.actionDigest),
                    "this declared input was not minted, so the region reads"
                            + " it concretely and no row states a value for"
                            + " it: " + ConcolicRegionRuntime.rootCause(throwable));
        }
    }

    /**
     * Whether a mint asked for under {@code label} did not happen: no symbol
     * {@code expression} names carries the label.  The VM mints nothing on a
     * JVM-wide object and never replaces an expression a value or a
     * reference field already carries; the refusal is named by which one,
     * and no row claims the mint.
     */
    private static boolean mintRefused(JsonElement expression, String label,
                                       boolean jvmShared, String what,
                                       String subject) {
        if (expression != null) {
            for (ExpressionWalk walk = ExpressionWalk.of(expression);
                 walk.hasNext(); ) {
                if (optionalString(walk.next(), "_exp").contains(label)) {
                    return false;
                }
            }
        }
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC, subject,
                "the VM minted no symbol on " + what + ": " + (jvmShared
                        ? "a JVM-wide object carries none"
                        : "it keeps the expression it already carried, which"
                        + " a mint never replaces") + "; the region reads it"
                        + " as it was and no row states a mint of it");
        return true;
    }

    /** What the VM says of {@code value}: whether it is JVM-wide. */
    private static boolean jvmShared(ConcolicVmBroker api, Object value) {
        try {
            JsonElement answer = JsonParser.parseString(api.expression(value));
            return answer.isJsonObject()
                    && answer.getAsJsonObject().has("jvmShared")
                    && answer.getAsJsonObject().get("jvmShared")
                    .getAsBoolean();
        } catch (Throwable unanswered) {
            return false;
        }
    }

    /** Keeps a VM-propagated value as this consumer's input authority. */
    private static boolean retainPropagatedInput(
            ActiveRegion active, SymbolizeAction action, Object value,
            JsonElement expression, String requestedSymbol,
            List<String> fieldPath, String fieldSignature) {
        if (!carriesInputAuthority(action, expression)) {
            return observeCutPortWithoutMinting(active, action);
        }
        RowRuntime.derivedRoot(action.symbol);
        active.pathRecordingStarted = true;
        active.recordManualSymbolization(action, requestedSymbol, fieldPath,
                fieldSignature, expression, false, true,
                ConcolicRegionRuntime.recordedScalar(value), 0L);
        return true;
    }

    /**
     * A declared communication cut port when nothing propagated into it yet:
     * never minted on.
     *
     * <p>The producer's expression is attached AFTER this hook runs, so a
     * mint here is a free root the attach overwrites, unconstrained in the
     * formula.  A value that never arrives is already named by
     * {@code RPC_ATTACH_SENDER_EXPRESSION_MISSING} and
     * {@code WIRE_FLOW_VALUE_UNBOUND}.  Opens path recording so the VM still
     * creates the read boundary; {@code true} means nothing left to do.</p>
     */
    private static boolean observeCutPortWithoutMinting(
            ActiveRegion active, SymbolizeAction action) {
        if (!declaredCommunicationCutPort(action)) return false;
        active.pathRecordingStarted = true;
        return true;
    }

    /**
     * What the VM carries in one cell: a container's own expression, else
     * the field's.
     */
    static JsonElement cellExpression(ConcolicVmBroker api, Object owner,
                                      String declaringClass, String fieldName,
                                      String descriptor, Object value)
            throws Exception {
        return ConcolicRegionRuntime.engineExpression(containerValue(value)
                ? api.expression(value)
                : api.fieldExpression(owner, declaringClass, fieldName,
                        descriptor, value));
    }

    private static boolean containerValue(Object value) {
        return value != null && (value.getClass().isArray()
                || value instanceof Map<?, ?>
                || value instanceof Set<?>
                || value instanceof Collection<?>);
    }

    /**
     * Whether a declared cell holds a container the VM already speaks for.
     *
     * <p>ONE TEST for every leaf-minting path ({@link #symbolizeField},
     * {@link #materializeField}, {@link #symbolize}): a container carries its
     * own expression, and a leaf minted on it would replace that with a free
     * variable.  Primitive paths need none: callers gate on
     * {@link ModelValues#isPrimitiveBox}.</p>
     */
    private static boolean declaredContainerCell(Object value) {
        return value != null && value != MissingValue.INSTANCE
                && containerValue(value);
    }

    /**
     * THE label of a declared mint, registered BEFORE the VM store
     * ({@link RowRuntime#declaredMintLabel}), so no activation closing on
     * another thread can publish the store as its own write.
     */
    private static String declaring(String label) {
        RowRuntime.declaredMintLabel(label);
        return label;
    }

    /**
     * Gives a manually minted primitive root the stable address of its
     * planned occurrence; reference labels keep their wire identity.
     */
    private static String manualMintLabel(String requestedSymbol,
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
                + ArtifactIO.sha256(occurrence);
    }

    /**
     * Whether the value that arrived is already this input's authority.
     *
     * <p>Any propagated expression, except for a DECLARED primitive root,
     * which asks the strict question (anything symbolic inside?): a
     * {@code ReadFrom} of constants would otherwise keep it concrete forever.
     * </p>
     */
    private static boolean carriesInputAuthority(
            SymbolizeAction action, JsonElement expression) {
        return action != null && action.declaredSymbolicRoot
                && JavaPrimitiveSmtSemantics.primitive(action.javaType)
                ? VmExpressionIr.carriesSymbolicValue(expression)
                : VmExpressionIr.carriesPropagatedValue(expression);
    }

    /**
     * Whether this action names a declared communication port, on either side
     * of the wire; same test as
     * {@code ConcolicScheduler.SymbolicInputSelection.declaredCutPort}.
     */
    private static boolean declaredCommunicationCutPort(
            SymbolizeAction action) {
        return action != null
                && RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT
                .equals(action.sourceKind);
    }
}
