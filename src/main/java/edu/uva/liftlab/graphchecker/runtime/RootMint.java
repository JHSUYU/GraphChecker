package edu.uva.liftlab.graphchecker.runtime;

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

import com.google.gson.JsonElement;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;
import edu.uva.liftlab.graphchecker.runtime.FieldAccess.MissingValue;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;

import java.lang.reflect.Field;
import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.List;

/**
 * R1 section 1.2 and R5's one mint-value decision: where a root's value
 * comes from, at every cell a plan can declare.
 *
 * <p>Six shapes of the same mint -- a root argument, an in-region helper
 * argument or local, an exact {@code getstatic}, a heap field reached
 * through an accessor, a receiver field, and a configured source's hook --
 * and ONE rule about the value: the VM is the authority.  A cell that
 * already carries a propagated expression keeps it
 * ({@link #retainPropagatedInput}), a container is left to the expression
 * it carries ({@link #declaredContainerCell}), a declared cut port is never
 * minted on ({@link #observeCutPortWithoutMinting}), and only what is left
 * becomes a symbol.</p>
 *
 * <p>ONE PLACE DECIDES A MINT'S VALUE: {@link #focusedRootValue}, asked by
 * every mint path, on the occurrence the RECORDING minted at.  A clock is
 * stated as a skew there rather than a value, and a mint the run cannot
 * place at the planned node and epoch refuses the model and keeps the
 * recording's value.</p>
 *
 * <p>Needs back from {@link ConcolicRegionRuntime}: the innermost
 * activation (or the one a root token owns), the expression import, the
 * path-recording gate, {@code recordedScalar}, and the one
 * declaring-region rule; plus the per-activation mint ledger ActiveRegion
 * holds.  The eight woven hook names and the external
 * {@code symbolizeConfiguredSourceField} stay there as delegates.</p>
 */
final class RootMint {
    private RootMint() {
    }

    /**
     * Called once per Java argument immediately after
     * {@link #enterRegionFrame}.
     */
    static void symbolizeArgument(long token, int argumentIndex,
                                         Object value, String primitiveValue) {
        ActiveRegion active = ConcolicRegionRuntime.ownerRegion(token);
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
                if ("ARGUMENT".equals(action.location)
                        && action.declaresArrayInput(
                        Collections.<String>emptyList())) {
                    symbolize(active, action, null, engine());
                }
                continue;
            }
            if ("ARGUMENT_FIELD_PATH".equals(action.location)) {
                if (action.fieldPaths.isEmpty()) {
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
    static void symbolizeMethodArgument(String method,
                                               int argumentIndex,
                                               Object value,
                                               String primitiveValue) {
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
     * Mints the declared root argument before ordinary Java control flow
     * consumes it.  Soot writes the returned value back to the parameter
     * local (including an unbox for primitive parameters).  No branch
     * outcome is overridden here: a primitive live-in becomes a symbol and
     * everything else is passed through as the program left it.
     */
    static Object materializeArgument(long token, int argumentIndex,
                                             Object boxedOrReference,
                                             String primitiveValue) {
        ActiveRegion active = ConcolicRegionRuntime.ownerRegion(token);
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
        }
        return boxedOrReference;
    }

    /** Mints a declared live-in at an exact in-region helper parameter. */
    static Object materializeMethodArgument(String method,
                                                   int argumentIndex,
                                                   Object boxedOrReference,
                                                   String primitiveValue) {
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
     * Materializes a primitive live-in and returns a fresh boxed value.  Soot
     * immediately unboxes this result back into the original local, allowing
     * the VM's symbolic field expression to flow into the actual branch.
     */
    static Object materializePrimitive(String method, int unitIndex,
                                              String local,
                                              Object boxedValue) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
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
     * Materializes the primitive value consumed by one exact {@code getstatic}
     * site.
     */
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
        List<SymbolizeAction> claimed = active.activation.symbolize;
        for (SymbolizeAction action : claimed) {
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
            try {
                ConcolicVmBroker api = engine();
                Field exactField = declaredInstanceField(leafOwner,
                        action.exactLeafFieldSignature());
                if (exactField == null) {
                    continue;
                }
                String leafFieldSignature = exactFieldSignature(exactField);
                Object value = exactField.get(leafOwner);
                JsonElement carried;
                try {
                    carried = containerValue(value)
                            ? ConcolicRegionRuntime.engineExpression(api.expression(value))
                            : ConcolicRegionRuntime.engineExpression(api.fieldExpression(leafOwner,
                            exactField.getDeclaringClass().getName(),
                            exactField.getName(), javaTypeDescriptor(
                            exactField.getType().getTypeName()), value));
                } catch (ConcolicRegionRuntime.PropagatedExpressionImportFailure unreadable) {
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
                if (declaredContainerCell(value)) {
                    // A container is symbolic only once a root-derived
                    // value is put into it, which the VM states inside the
                    // expression it then carries.
                    continue;
                }
                MintedLeaf minted = mintExactFieldLeaf(active, action,
                        api, leafOwner, leafFieldSignature, action.symbol,
                        value);
                if (minted == null) continue;
                active.recordManualSymbolization(action, action.symbol,
                        action.fieldPath, leafFieldSignature,
                        minted.expression, true, false,
                        minted.recordedValue);
            } catch (Throwable throwable) {
                // The declaration said the search starts at this cell and
                // it was not minted, so the region reads it concretely and
                // the composer meets a read with no root.  Stated, never
                // swallowed: a mint that failed and a cell the plan never
                // named read identically from the corpus.
                RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNSTATED_VALUE,
                        edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC,
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
     * <p>A declared configured source is ONE symbol.  The frozen catalog
     * says only WHERE its hook sites are; every read of a declared site --
     * in this occurrence, in another occurrence, in another session -- binds
     * to that site's one symbol, and neither the occurrence nor which read
     * of it this was is part of the symbol's identity.</p>
     *
     * <p>They used to be.  The catalog was SIZED by the executions the
     * recording happened to make, a read past that size was refused
     * {@code DECLARATION_MISSING ... occurrence 2 exceeds the frozen phase
     * catalog size 1}, and the VM label of read n&gt;1 carried the entry
     * number -- so one declared marker became several unconstrained
     * variables, a flip moved one of them, and the reads that took the
     * others kept the recorded value.</p>
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
            return phase == null ? "" : phase.phaseId();
        }
    }

    /**
     * THE ACTIVATION THAT OWNS THIS MINT, or {@code null} when no admitted
     * activation of this session does.
     *
     * <p>One predicate, asked by every mint entry -- the configured source,
     * the manual field, the heap field, the clock -- before anything is
     * symbolized, because they all owe the same thing: a mint that
     * symbolizes puts a SYMBOL into the VM, every later expression of the
     * session carries it, and the only thing that makes that symbol
     * answerable is the {@link edu.uva.liftlab.graphchecker.contract
     * .RootMintRow} its activation publishes.  So the two are one decision:
     * a mint this run can address is symbolized AND rowed; a mint it cannot
     * is refused by name and the region reads the recording's own value.</p>
     *
     * <p>Addressed at the region whose plan OWNS the root
     * ({@link ConcolicRegionRuntime#declaringRegion}), the same walk
     * {@link #focusedRootValue} and {@code ActiveRegion#mintOccurrence}
     * make, so all three resolve one mint the same way.  An activation with
     * no {@code d3Address} was not admitted -- {@code
     * RowRuntime#beginActivation} states LINEAGE_LOST and returns none --
     * and a session that is not open has nowhere to publish a row at
     * all.</p>
     */
    static ActiveRegion mintOwner(ActiveRegion active, String rootId) {
        if (active == null || !RowRuntime.open()) return null;
        ActiveRegion owner = ConcolicRegionRuntime.declaringRegion(
                new ConcolicRegionRuntime.Declares.Root(safe(rootId)));
        if (owner == null) owner = active;
        return owner.d3Address == null ? null : owner;
    }

    /**
     * Refuses one mint nothing admitted owns: the value stays concrete and
     * the session states MINT_UNATTRIBUTED naming the root and where it
     * stood.
     *
     * <p>BLOCKING when the obligation this session runs ASSIGNS the root --
     * the replay then ran the recording's value where the wave asked for
     * another one, which is a session that did not run what was asked --
     * and DIAGNOSTIC otherwise, where it says only that this run read the
     * recording's own value at a declared site.  Never a symbol without a
     * row: the alternative branch of this one decision publishes the mint
     * row ({@code RowPlaceholderMint#roots}), and the two are exhaustive.</p>
     */
    static boolean mintUnattributed(ActiveRegion active, String rootId,
                                    String context) {
        if (mintOwner(active, rootId) != null) return false;
        RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                        .MINT_UNATTRIBUTED,
                assignedByTheWave(rootId)
                        ? edu.uva.liftlab.graphchecker.contract.GapClass
                                .BLOCKING
                        : edu.uva.liftlab.graphchecker.contract.GapClass
                                .DIAGNOSTIC,
                firstNonBlank(safe(rootId), safe(context)),
                "no admitted activation of this session owns this mint ("
                        + safe(context) + "), so the declared root is read"
                        + " concretely and no symbol is minted for it");
        return true;
    }

    /** Whether the obligation this session runs assigns this root. */
    private static boolean assignedByTheWave(String rootId) {
        return !edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                .rootAssignment(safe(rootId)).isEmpty()
                || edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                        .clockSkew(safe(rootId)) != null;
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
    static boolean configuredSource(
            String sourceId, Object owner, String fieldSignature) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        // Nothing to mint ON is not a gap: the site simply was not carrying a
        // declared owner on this entry.
        if (owner == null) return false;
        // WHERE the hook fired decides whether it may mint at all: a region
        // running concretely contributes the literals it read, never a free
        // root (README SS9 rule 1).  Asked first, because a catalog refusal
        // is a statement about the occurrence that OWNS the site, and an
        // occurrence running concretely owns no mint to refuse.
        if (!ActiveRegion.mintsUnderSymbolicOccurrence(active, safe(sourceId),
                safe(fieldSignature))) {
            return false;
        }
        SourceSiteEntry entry = active.observeConfiguredSourceEntry(
                safe(sourceId), safe(fieldSignature));
        if (entry == null) return false;
        ConcolicRegionRuntime.beginBookkeeping();
        try {
            Field field = declaredInstanceField(owner, safe(fieldSignature));
            if (field == null || !field.getType().isPrimitive()) {
                return false;
            }
            // Asked before the VM is touched: a mint nothing admitted owns
            // publishes no row, so symbolizing here would leave the session
            // carrying a symbol no row of it resolves.
            if (mintUnattributed(active, safe(sourceId),
                    "configured source at " + entry.siteId)) {
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
                carried = ConcolicRegionRuntime.engineExpression(api.fieldExpression(owner,
                        declaringClass, field.getName(), descriptor,
                        field.get(owner)));
            } catch (ConcolicRegionRuntime.PropagatedExpressionImportFailure unreadable) {
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
            // WHAT THE REGION OBSERVED, read before anything is written:
            // the live value at this mint, which in a focused replay is the
            // recording's own.  Asked here and not after the plant, because
            // after the plant the cell holds the wave's value and the two
            // quantities are no longer distinguishable off the heap.
            String observed = ConcolicRegionRuntime.recordedScalar(
                    field.get(owner));
            // The application's Map re-key reads the assigned value back
            // through this same path, so the wave's value is written first.
            String planted = "";
            if (!reused) {
                planted = applyFocusedRootAssignment(active, safe(sourceId),
                        owner, safe(fieldSignature), descriptor);
            }
            // ONE SYMBOL PER DECLARED SOURCE.  The label is derived from
            // the declared site and from nothing this read is: the same leaf
            // is asked for at every read of it, so the composer meets one
            // variable and a solver that flips it flips it everywhere.  The
            // row below still states one mint per READ -- that is the
            // evidence of where it was observed -- and the reads join to the
            // one symbol.
            String symbol = ConfiguredSourcePhaseContract
                    .engineLabelForPhase(entry.phaseId(), safe(sourceId));
            if (!reused) {
                api.symbolizeExactField(owner, exactFieldSignature(field),
                        symbol);
            }
            // The mint is a symbolic write, so the VM has started this
            // field's version log by itself; the declaration that used to be
            // filed here bought nothing that the write did not already do.
            ConcolicRegionRuntime.ensurePathRecordingStarted(active);
            Object value = field.get(owner);
            JsonElement expression = ConcolicRegionRuntime.engineExpression(api.fieldExpression(
                    owner, declaringClass, field.getName(), descriptor,
                    value));
            // A MINT THAT PLANTED STATES WHAT IT RAN AT, not what it
            // observed.  0dd03aec7 left this half owed -- "the mint that
            // PLANTS a root should state what it ran it at ... until then
            // the ask is the only statement of it" -- and until it was paid
            // a successful plant published the RECORDING's value, so the
            // corpus stated one replay's root twice and differently and
            // Composer refused the path.  That is what hdfs-17960's only
            // witness died of: the mint said "true", the obligation
            // assigned "false", and the replay had printed the real fault.
            //
            // A CLOCK is left alone.  The wave states a clock as a SKEW on
            // this run's own instant, and the mint's reading is the instant
            // FlipQuery floors and ceilings the cell by; overwriting it
            // with the skewed value would move the floor off the reading it
            // is defined against.
            String stated = !planted.isEmpty()
                    && edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                            .clockSkew(safe(sourceId)) == null
                    ? planted : observed;
            active.recordConfiguredSourceMint(entry, safe(sourceId),
                    safe(fieldSignature), symbol, expression, reused,
                    stated);
            return true;
        } catch (Throwable failure) {
            return false;
        } finally {
            ConcolicRegionRuntime.endBookkeeping();
        }
    }

    /**
     * The value the wave asks of this root at its mint, or {@code ""}.
     *
     * <p>One decision for every mint, whatever the mint writes into.  Only
     * on an occurrence of the FOCUSED SET ({@code FocusedReplay#focused}):
     * the flipped occurrence, a member of its factor, or the MINT of a root
     * the obligation assigns, which the focus row names because a value can
     * only be planted where the run mints it.  Applying it in a region that
     * merely runs alongside would make the run state something the
     * obligation never asked.</p>
     *
     * <p>A clock is stated as a SKEW rather than a value, because every
     * execution reads a clock fresh: the focus row says how far off the
     * reading is to be and this adds it to {@code observed}, the instant
     * this run actually read.  Pinning a replay to the recording's instant
     * is what left eleven of bug3's twelve paths unsatisfiable at every
     * valuation.</p>
     */
    static String focusedRootValue(ActiveRegion active,
                                           String rootId, Object observed) {
        edu.uva.liftlab.graphchecker.runtime.FocusedReplay.mintReached(
                rootId);
        if (active == null) return "";
        // AT THE REGION THAT OWNS THE MINT, not at whichever activation was
        // innermost when the site ran: the focus row addresses each mint by
        // the occurrence the RECORDING minted it at (rootMints), so the two
        // passes can only join if both resolve the mint the same way.
        ActiveRegion owner = ConcolicRegionRuntime.declaringRegion(
                new ConcolicRegionRuntime.Declares.Root(safe(rootId)));
        if (owner == null) owner = active;
        if (owner.d3Address == null) return "";
        if (!edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                .focused(owner.d3Address)) {
            return "";
        }
        Long skew = edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                .clockSkew(rootId);
        if (skew == null) {
            return edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                    .rootAssignment(rootId);
        }
        Long reading = readingOf(observed);
        if (reading == null) {
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                            .UNPRODUCIBLE_ANSWER,
                    edu.uva.liftlab.graphchecker.contract.GapClass
                            .BLOCKING, rootId,
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
     * @return the value it wrote, or {@code ""} when it wrote none.  The
     *         mint states it, because a replay that PLANTED a root ran it at
     *         the value the wave asked and not at the one it observed.
     */
    private static String applyFocusedRootAssignment(
            ActiveRegion active, String sourceId, Object owner,
            String fieldSignature, String descriptor) {
        String value = focusedRootValue(active, sourceId,
                readExactField(owner, fieldSignature));
        if (value.isEmpty()) return "";
        if (!active.mintIsPlaceable(owner)) return "";
        if (writeModeledField(owner, fieldSignature, descriptor, value)) {
            // Filed where the value was WRITTEN: a mint that asked and could
            // not place the write kept the recording's value, and the
            // session says so with ASSIGNMENT_UNPLANTED rather than letting
            // the composer be the first to notice.
            edu.uva.liftlab.graphchecker.runtime.FocusedReplay.planted(
                    sourceId);
            return value;
        }
        RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                        .UNPRODUCIBLE_ANSWER,
                edu.uva.liftlab.graphchecker.contract.GapClass
                        .BLOCKING, sourceId,
                "the wave's assignment for this root could not be"
                        + " written into " + fieldSignature);
        return "";
    }

    static void symbolizeReceiverFields(ActiveRegion active,
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
                return;
            }
            JsonElement carried = containerValue(value)
                    ? ConcolicRegionRuntime.engineExpression(api.expression(value))
                    : ConcolicRegionRuntime.engineExpression(api.fieldExpression(owner,
                    field.owner(), field.name(),
                    javaTypeDescriptor(field.type()), value));
            if (retainPropagatedInput(active, action, value, carried, symbol,
                    exactFieldPath, leafFieldSignature)) {
                return;
            }
            if (declaredContainerCell(value)) {
                return;
            }
            MintedLeaf minted = mintExactFieldLeaf(active, action, api,
                    owner, leafFieldSignature, symbol, value);
            if (minted == null) return;
            active.recordManualSymbolization(action, symbol, exactFieldPath,
                    leafFieldSignature, minted.expression, true, false,
                    minted.recordedValue);
        } catch (Throwable throwable) {
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC, symbol,
                    "this declared field input was not minted, so the region"
                            + " reads it concretely and no row states a"
                            + " value for it: " + ConcolicRegionRuntime.rootCause(throwable));
        }
    }

    /**
     * Mints the scalar leaf of one exact field read: the expression the VM
     * carries afterwards and what the row may state as recorded, or {@code
     * null} when the leaf has no resolvable declaration (filed as
     * unresolved).
     *
     * <p>One rule, one implementation.  The receiver-field hook
     * ({@link #symbolizeField}) and the heap-field hook
     * ({@link #materializeField}) reach the same decision by the same
     * route -- {@link #retainPropagatedInput} said nothing propagated into
     * this input and the action is a declaration, so the search starts
     * here -- and only the first of them used to act on it.  The second refused with "exact input has no
     * propagated VM expression", which is how hdfs-17960's declared
     * {@code <AtomicInteger: int value>} region input stayed concrete: the
     * accessor materialization is a {@code HEAP_OBJECT_FIELD} action, so
     * it arrived at the hook that refused.</p>
     *
     * <p>And the wave's value reaches a field mint HERE, through the same
     * one decision every other mint asks ({@link #focusedRootValue}).  It
     * did not: a declared INTEGRAL cell minted through this path published
     * the value the recording read, whatever the obligation assigned, and
     * the composer met the contradiction instead of the plant -- on 11741
     * session {@code 869a1f0e285913ad-6f59cb84} the mint of {@code
     * HDFS.BLOCK_KEY.SERIAL_NO} states 182907 under an obligation assigning
     * 182910, which is one BLOCKING refusal per such root.</p>
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
        // The plant wrote into the cell this mint stands on, so the leaf the
        // VM is handed is what the region will now read, not what it held.
        // Re-read in both cases: nothing else writes this cell between the
        // read above and here, so with no plant the re-read IS what it held
        // and no flag has to carry whether a plant happened -- which is what
        // let "the row states no value" stand in for "a plant happened".
        Object held = readExactField(owner, leafFieldSignature);
        if (held == MissingValue.INSTANCE) held = value;
        api.symbolizeExactField(owner, leafFieldSignature,
                manualMintLabel(symbol, active.activation.occurrenceId,
                        JavaPrimitiveSmtSemantics.primitive(
                                field.type())));
        ConcolicRegionRuntime.ensurePathRecordingStarted(active);
        return new MintedLeaf(ConcolicRegionRuntime.engineExpression(api.fieldExpression(owner,
                field.owner(), field.name(), descriptor, held)), recorded);
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
     * Plants the wave's value at one field mint and states what that mint
     * OBSERVED there: two questions, two answers, one after the other.
     *
     * <p>ONE PLACE DECIDES A MINT'S VALUE, and every mint path asks it: the
     * manual primitive ({@link #materializePrimitiveValue}), the configured
     * source ({@link #symbolizeConfiguredSourceField}), the clock (a skew,
     * inside {@link #focusedRootValue}) and the manual field here.  A path
     * that minted a declared root without asking left the replay running the
     * recording's value under an obligation that asked for another one.</p>
     *
     * <p>AND A MINT ROW ALWAYS STATES WHAT THE REGION OBSERVED.  It used to
     * state {@code ""} whenever a plant followed, on the ground that a
     * counterfactual is not a recording -- but {@code value} is not the
     * counterfactual: it is the live value this region read at the mint,
     * before anything was written, which in a focused replay is the
     * recording's own.  The session's valuation is stated by the FOCUS row
     * and by nothing here.  Blanking it is what published {@code
     * roots.jsonl seq=121 field=recordedValue
     * HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED=} in hdfs-17960's two focused
     * sessions (793875fb…, cb67875d…) and one empty CLOCK row in each of
     * hdfs-11741's six -- the very root each obligation moves -- and a root
     * whose row states no value has no centre for a relative domain to
     * resolve against, so IMPORT refuses it under invariant 8 and the
     * composer could not move it at all.</p>
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
        if (leafOwner == MissingValue.INSTANCE) {
            return;
        }
        if (leafOwner == null) {
            return;
        }
        symbolizeField(active, action, leafOwner, label, path, api);
    }

    private static Object materializePrimitiveValue(
            ActiveRegion active, SymbolizeAction action, Object concrete,
            List<String> path) {
        // The mint RAN, whatever it goes on to do with the wave's value.
        edu.uva.liftlab.graphchecker.runtime.FocusedReplay.mintReached(
                action.symbol);
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
        if (retainPropagatedInput(active, action, concrete, carried,
                action.symbol, exactPath, fieldSignature)) {
            return concrete;
        }
        if (mintUnattributed(active, action.symbol,
                "declared primitive input at "
                        + firstNonBlank(fieldSignature, action.cell))) {
            return concrete;
        }
        // The wave's value reaches a manual root here, because the cell a
        // manual mint stands on IS the box the region reads back -- the
        // same decision the declared field's writer takes
        // (#focusedRootValue), so a clock's skew applies wherever the clock
        // is read and not only where a configured source happens to be.
        String assigned = focusedRootValue(active, action.symbol, concrete);
        Object planted = concrete;
        if (!assigned.isEmpty()) {
            Object modeled = ModelValues.coerce("", assigned,
                    concrete == null ? null : concrete.getClass());
            if (modeled == null
                    || modeled == ModelValues.UnsupportedReplayValue.INSTANCE) {
                RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                                .UNPRODUCIBLE_ANSWER,
                        edu.uva.liftlab.graphchecker.contract.GapClass
                                .BLOCKING, action.symbol,
                        "the wave's value for this root could not be read as"
                                + " the type the mint reads");
                assigned = "";
            } else {
                planted = modeled;
            }
        }
        Object fresh = freshPrimitiveBox(planted);
        try {
            api.symbolizeField(fresh, "value", manualMintLabel(action.symbol,
                    active.activation.occurrenceId, true));
            ConcolicRegionRuntime.ensurePathRecordingStarted(active);
            JsonElement expression = primitiveBoxExpression(api, fresh);
            active.recordManualSymbolization(action, action.symbol,
                    exactPath, fieldSignature, expression, true, false,
                    // WHAT THIS REGION OBSERVED, whether or not a plant
                    // followed: `concrete` is the value the mint was handed,
                    // and the plant above builds a FRESH box rather than
                    // writing into it, so this is the live read and never the
                    // wave's value.  The wave's value is the focus row's
                    // statement; a row that states neither leaves the root
                    // with no centre for its domain (invariant 8).
                    ConcolicRegionRuntime.recordedScalar(concrete));
            if (!assigned.isEmpty()) {
                edu.uva.liftlab.graphchecker.runtime.FocusedReplay.planted(
                        action.symbol);
            }
            return fresh;
        } catch (Throwable throwable) {
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
        return ConcolicRegionRuntime.engineExpression(api.fieldExpression(boxed,
                boxed.getClass().getName(), "value", descriptor, boxed));
    }

    /**
     * Writes one value the wave stated into one exact field.
     *
     * <p>The one place a replay's own value reaches the workload's heap:
     * the focus row states it (a root assignment, or an answer at an
     * attach) and this writes it where the declared cell is.</p>
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
            api.symbolize(value, manualMintLabel(action.symbol,
                    active.activation.occurrenceId,
                    isPrimitiveBox(value)));
            ConcolicRegionRuntime.ensurePathRecordingStarted(active);
            JsonElement expression = value == null ? null
                    : ConcolicRegionRuntime.engineExpression(api.expression(value));
            active.recordManualSymbolization(action, action.symbol,
                    Collections.<String>emptyList(), "", expression,
                    true, false);
        } catch (Throwable throwable) {
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC,
                    firstNonBlank(action.symbol, action.actionDigest),
                    "this declared input was not minted, so the region reads"
                            + " it concretely and no row states a value for"
                            + " it: " + ConcolicRegionRuntime.rootCause(throwable));
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
        ConcolicRegionRuntime.ensurePathRecordingStarted(active);
        active.recordManualSymbolization(action, requestedSymbol, fieldPath,
                fieldSignature, expression, false, true,
                ConcolicRegionRuntime.recordedScalar(value));
        return true;
    }

    /**
     * A declared communication cut port when nothing propagated into it yet.
     *
     * <p>Every caller of {@link #retainPropagatedInput} treats {@code false}
     * as permission to mint, and a cut port must not take it.  The value at
     * such a port is produced on the other side of the wire, and the
     * instrumented frame installs the producer's expression with
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
     * own handoff gap, by {@code RPC_ATTACH_SENDER_EXPRESSION_MISSING} and
     * by the composition's {@code WIRE_FLOW_VALUE_UNBOUND}; a mint hid all
     * three behind a root that
     * answered to nothing.</p>
     *
     * <p>Open path recording so the VM still resolves the writer and creates
     * the read boundary, and return {@code true} to say the caller has
     * nothing left to do.  Every other action that reaches this point was
     * declared by the case, so minting is exactly what it asked for.</p>
     */
    private static boolean observeCutPortWithoutMinting(
            ActiveRegion active, SymbolizeAction action) {
        if (!declaredCommunicationCutPort(action)) return false;
        ConcolicRegionRuntime.ensurePathRecordingStarted(active);
        return true;
    }

    static boolean containerValue(Object value) {
        return value != null && (value.getClass().isArray()
                || value instanceof Map<?, ?>
                || value instanceof Set<?>
                || value instanceof Collection<?>);
    }

    /**
     * Whether a declared cell holds a container the VM already speaks for.
     *
     * <p>ONE TEST, taken by every path that would mint a leaf on a declared
     * cell: the receiver-field hook ({@link #symbolizeField}), the
     * heap-field hook ({@link #materializeField}) and the argument/local
     * hook ({@link #symbolize}).  A container is symbolic only once a
     * root-derived value is put into it, and the VM states that inside the
     * expression the container then carries, so a fresh leaf minted on it
     * would replace a propagated expression with a free variable.</p>
     *
     * <p>The heap-field hook used to hold this test with an EMPTY body --
     * its {@code continue} had been absorbed into the comment text -- so a
     * declared container reached through that hook alone fell through to
     * {@code mintExactFieldLeaf}.  The three now share one predicate so
     * the next such divergence cannot be written.</p>
     *
     * <p>The primitive mint paths ({@link #materializePrimitiveValue},
     * {@link #materializeStaticPrimitiveField}) take no container test and
     * need none: every caller gates on {@link ModelValues#isPrimitiveBox}
     * or on a
     * primitive-typed field, so a container cannot reach them.</p>
     */
    private static boolean declaredContainerCell(Object value) {
        return value != null && value != MissingValue.INSTANCE
                && containerValue(value);
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
                + ArtifactIO.sha256(occurrence);
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
                && JavaPrimitiveSmtSemantics.primitive(action.javaType)
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
}
