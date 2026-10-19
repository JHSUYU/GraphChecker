package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.causynth.LibraryCatalog;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.Digests;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.UnplannedInput;
import edu.uva.liftlab.graphchecker.contract.Validity;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;
import edu.uva.liftlab.graphchecker.runtime.FieldAccess.MissingValue;
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

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;
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

final class RootMint {
    private static final Set<String> CLOCK_READINGS =
            ConcurrentHashMap.newKeySet();
    private static final Map<String, String> CONFIGURATIONS =
            new ConcurrentHashMap<>();

    private RootMint() {
    }

    static boolean configurationAgrees(String rootId, String value,
                                       String where) {
        String standing = CONFIGURATIONS.putIfAbsent(nonNull(rootId),
                nonNull(value));
        if (standing == null || standing.equals(nonNull(value))) return true;
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                nonNull(rootId), "the configuration read at " + nonNull(where)
                        + " ran at " + nonNull(value) + " where the root's"
                        + " symbol stands for " + standing + " in this JVM"
                        + " (another default, view or node's"
                        + " configuration), so it is read concretely and no"
                        + " row states a mint of it");
        return false;
    }

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

    static Object materializePrimitive(String method, int unitIndex,
                                              String local,
                                              Object boxedValue) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active == null || boxedValue == null) {
            return boxedValue;
        }
        int occurrence = active.materializationOccurrences.local(
                method, unitIndex, local);
        SymbolizeAction marker = null;
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesLocal(method, unitIndex, local)) continue;
            if (marker == null
                    && LibraryCatalog.rootsNothing(action.marker)) {
                marker = action;
            }
            if (!action.acceptsOccurrence(occurrence)
                    || !action.repeatedPrimitiveAccessor()
                    && !active.materialized.add(action.symbol)) {
                continue;
            }
            return materializePrimitiveValue(active, action, boxedValue,
                    null);
        }
        if (marker != null) unplanned(active, marker, occurrence);
        return boxedValue;
    }

    private static void unplanned(ActiveRegion active, SymbolizeAction marker,
                                  int k) {
        if (k > UnplannedInput.MAX + 1) return;
        try {
            UnplannedInput input = UnplannedInput.of(
                    active.activation.taskId, marker.symbol, k);
            RowRuntime.gap(GapKind.UNPLANNED_INPUT, GapClass.DIAGNOSTIC,
                    input.subject(), "the marker " + marker.marker + " at "
                            + firstNonBlank(marker.siteId, marker.cell)
                            + " ran its call #" + k + " of this occurrence, "
                            + "which its task plans no input for, so it ran "
                            + "concretely; an admitted session that may "
                            + "parent grows it into the input "
                            + input.grown());
        } catch (RuntimeException unnamed) {
        }
    }

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

    static final class SourceSiteEntry {
        private final ConfiguredSourcePhaseContract.Occurrence phase;
        final String siteId;
        SourceSiteEntry(
                ConfiguredSourcePhaseContract.Occurrence phase,
                String siteId) {
            this.phase = phase;
            this.siteId = nonNull(siteId);
        }

        String phaseId() {
            return phase.phaseId();
        }

        RootCategory category() {
            return phase.category();
        }

        String domainMin() {
            return phase.domainMin();
        }

        String domainMax() {
            return phase.domainMax();
        }

        Validity valid() {
            return phase.valid();
        }
    }

    static ActiveRegion mintOwner(ActiveRegion active, String rootId) {
        if (active == null || !RowRuntime.open()) return null;
        ActiveRegion owner = active.rootOwner(rootId);
        return owner.d3Address == null ? null : owner;
    }

    static boolean mintUnattributed(ActiveRegion active, String rootId,
                                    String context) {
        if (mintOwner(active, rootId) != null) return false;
        RowRuntime.gap(GapKind.MINT_UNATTRIBUTED,
                assignedByTheWave(rootId)
                        ? GapClass.BLOCKING
                        : GapClass.DIAGNOSTIC,
                firstNonBlank(nonNull(rootId), nonNull(context)),
                "no admitted activation of this session owns this mint ("
                        + nonNull(context) + "), so the declared root is read"
                        + " concretely and no symbol is minted for it; the"
                        + " read stands at no occurrence, so no reading of"
                        + " it guards the arms that rest on it");
        return true;
    }

    private static boolean assignedByTheWave(String rootId) {
        return !FocusedReplay.rootAssignment(nonNull(rootId)).isEmpty()
                || FocusedReplay.clockSkew(nonNull(rootId)) != null;
    }

    static boolean configuredSource(
            String sourceId, Object owner, String fieldSignature) {
        if (owner == null) return false;
        if (RecordingPlant.planting()) {
            RecordingPlant.hook(nonNull(sourceId), owner,
                    nonNull(fieldSignature));
            return false;
        }
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (mintConfiguredSource(active, nonNull(sourceId), owner,
                nonNull(fieldSignature))) {
            return true;
        }
        ConcolicRegionRuntime.pauseObservation();
        try {
            readConcretely(active, nonNull(sourceId),
                    readExactField(owner, nonNull(fieldSignature)));
        } catch (Throwable ignored) {
        } finally {
            ConcolicRegionRuntime.resumeObservation();
        }
        return false;
    }

    private static boolean mintConfiguredSource(ActiveRegion active,
                                                String sourceId, Object owner,
                                                String fieldSignature) {
        if (!ActiveRegion.mintsUnderSymbolicOccurrence(active, sourceId,
                fieldSignature)) {
            return false;
        }
        SourceSiteEntry entry = active.observeConfiguredSourceEntry(
                nonNull(sourceId), nonNull(fieldSignature));
        if (entry == null) return false;
        ConcolicRegionRuntime.pauseObservation();
        try {
            Field field = declaredInstanceField(owner, nonNull(fieldSignature));
            if (field == null || !field.getType().isPrimitive()) {
                return false;
            }
            if (mintUnattributed(active, nonNull(sourceId),
                    "configured source at " + entry.siteId)) {
                return false;
            }
            ConcolicVmBroker api = engine();
            String declaringClass = field.getDeclaringClass().getName();
            String descriptor = javaTypeDescriptor(
                    field.getType().getTypeName());
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
            boolean reused = VmExpressionIr.carriesSymbolicValue(carried);
            if (reused) RowRuntime.derivedRoot(sourceId);
            String observed = ConcolicRegionRuntime.recordedScalar(
                    field.get(owner));
            if (!reused && entry.category() == RootCategory.CONFIG
                    && !configurationAgrees(nonNull(sourceId), observed,
                    entry.siteId)) {
                return false;
            }
            String planted = "";
            if (!reused && entry.category() != RootCategory.CONFIG) {
                planted = applyFocusedRootAssignment(active, nonNull(sourceId),
                        owner, nonNull(fieldSignature), descriptor);
            }
            String symbol = ConfiguredSourcePhaseContract.engineLabel(
                    nonNull(sourceId));
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
                            + nonNull(fieldSignature), nonNull(sourceId))) {
                return false;
            }
            active.pathRecordingStarted = true;
            String stated = !planted.isEmpty()
                    && FocusedReplay.clockSkew(nonNull(sourceId)) == null
                    ? planted : observed;
            active.recordConfiguredSourceMint(entry, nonNull(sourceId),
                    nonNull(fieldSignature), symbol, expression, reused,
                    stated);
            return true;
        } catch (Throwable failure) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE,
                    assignedByTheWave(nonNull(sourceId)) ? GapClass.BLOCKING
                            : GapClass.DIAGNOSTIC,
                    nonNull(sourceId), "the configured source at "
                            + entry.siteId + " was not minted, so the region"
                            + " reads " + nonNull(fieldSignature) + " as it was"
                            + " and no row states a mint of it: "
                            + ConcolicRegionRuntime.rootCause(failure));
            return false;
        } finally {
            ConcolicRegionRuntime.resumeObservation();
        }
    }

    private static void readConcretely(ActiveRegion active, String rootId,
                                       Object value) {
        if (active == null) return;
        String occurrence = active.rootOwner(rootId).address();
        if (occurrence.isEmpty()) return;
        RowRuntime.concreteReading(rootId, occurrence,
                ConcolicRegionRuntime.recordedScalar(value));
    }

    static void configuration(String sourceId, Object owner,
                              String fieldSignature) {
        if (owner == null) return;
        try {
            String assigned = FocusedReplay.rootAssignment(nonNull(sourceId));
            if (!assigned.isEmpty()) {
                plantConfiguration(nonNull(sourceId), owner,
                        nonNull(fieldSignature), assigned);
            }
            configuredSource(sourceId, owner, fieldSignature);
        } catch (Throwable failure) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE,
                    assignedByTheWave(nonNull(sourceId)) ? GapClass.BLOCKING
                            : GapClass.DIAGNOSTIC,
                    nonNull(sourceId), "the configuration read of "
                            + nonNull(fieldSignature) + " failed, so the region"
                            + " reads the field as it was and no row states a"
                            + " mint of it: "
                            + ConcolicRegionRuntime.rootCause(failure));
        }
    }

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
            String read = ConcolicRegionRuntime.recordedScalar(
                    field.get(owner));
            if (writeModeledField(owner, fieldSignature, descriptor, value)) {
                FocusedReplay.planted(sourceId, !value.trim().equals(read));
                return;
            }
            RowRuntime.gap(GapKind.UNPRODUCIBLE_ANSWER, GapClass.BLOCKING,
                    sourceId, "the wave's assignment for this configuration"
                            + " could not be written into "
                            + fieldSignature);
        } catch (Throwable failure) {
            RowRuntime.gap(GapKind.UNPRODUCIBLE_ANSWER, GapClass.BLOCKING,
                    sourceId, "the wave's assignment for this configuration"
                            + " could not be written into " + fieldSignature
                            + ": " + ConcolicRegionRuntime.rootCause(failure));
        } finally {
            ConcolicRegionRuntime.resumeObservation();
        }
    }

    static String focusedRootValue(ActiveRegion active,
                                           String rootId, Object observed) {
        FocusedReplay.mintReached(rootId);
        if (active == null) return "";
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

    private static Long readingOf(Object value) {
        return value instanceof Number && !(value instanceof Float)
                && !(value instanceof Double)
                ? Long.valueOf(((Number) value).longValue()) : null;
    }

    private static String applyFocusedRootAssignment(
            ActiveRegion active, String sourceId, Object owner,
            String fieldSignature, String descriptor) {
        Object observed = readExactField(owner, fieldSignature);
        String value = focusedRootValue(active, sourceId, observed);
        if (value.isEmpty()) return "";
        if (!active.mintIsPlaceable(owner)) return "";
        if (writeModeledField(owner, fieldSignature, descriptor, value)) {
            FocusedReplay.planted(sourceId, !value.trim().equals(
                    ConcolicRegionRuntime.recordedScalar(observed)));
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
        String symbol = action.symbol + "." + nonNull(symbolicPath);
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

    private static final class MintedLeaf {
        private final JsonElement expression;
        private final String recordedValue;

        private MintedLeaf(JsonElement expression, String recordedValue) {
            this.expression = expression;
            this.recordedValue = recordedValue;
        }
    }

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
        if (retainPropagatedInput(active, action, concrete, carried,
                action.symbol, exactPath, fieldSignature)) {
            return concrete;
        }
        if (mintUnattributed(active, action.symbol,
                "declared primitive input at "
                        + firstNonBlank(fieldSignature, action.cell))) {
            return concrete;
        }
        ActiveRegion owner = active.rootOwner(action.symbol);
        String node = owner.d3Address.node().render();
        boolean clock = action.declaresWallClockRead()
                && readingOf(concrete) != null;
        Object ran = clock ? clockReading(node, action, concrete) : concrete;
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
            if (!configurationAgrees(root, ConcolicRegionRuntime
                    .recordedScalar(planted), firstNonBlank(action.siteId,
                    action.cell))) {
                return concrete;
            }
            Object read = active.configurationRead(root, action.symbol);
            if (read != null) return read;
        }
        if (action.clock != null && !CLOCK_READINGS.add(owner.address()
                + "|" + action.symbol)) {
            return ran;
        }
        Object fresh = freshPrimitiveBox(planted);
        try {
            api.symbolizeField(fresh, "value", declaring(config
                    ? ConfiguredSourcePhaseContract.engineLabel(root)
                    : manualMintLabel(action.symbol,
                    active.activation.occurrenceId, true)));
            active.pathRecordingStarted = true;
            JsonElement expression = primitiveBoxExpression(api, fresh);
            active.recordManualSymbolization(action, action.symbol,
                    exactPath, fieldSignature, expression, true, false,
                    ConcolicRegionRuntime.recordedScalar(planted),
                    clock ? clockSkew(node, action, concrete, planted,
                            !assigned.isEmpty()) : 0L);
            if (!assigned.isEmpty()) {
                FocusedReplay.planted(root, !ConcolicRegionRuntime
                        .recordedScalar(planted).equals(ConcolicRegionRuntime
                                .recordedScalar(ran)));
            }
            if (config) active.configurationMinted(root, fresh);
            if (Boolean.TRUE.equals(fresh)) {
                Identity.doorFaulted(action.marker);
            }
            if (!action.marker.isEmpty()) {
                ConcolicRegionRuntime.openDoorWindow(active);
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

    private static JsonElement primitiveBoxExpression(
            ConcolicVmBroker api, Object boxed) throws Exception {
        if (boxed == null) return null;
        String descriptor = JavaPrimitiveBoxing.primitiveDescriptor(
                boxed.getClass().getName());
        if (descriptor.isEmpty()) return null;
        return ConcolicRegionRuntime.engineExpression(api.fieldExpression(boxed,
                boxed.getClass().getName(), "value", descriptor, boxed));
    }

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

    private static boolean observeCutPortWithoutMinting(
            ActiveRegion active, SymbolizeAction action) {
        if (!declaredCommunicationCutPort(action)) return false;
        active.pathRecordingStarted = true;
        return true;
    }

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

    private static boolean declaredContainerCell(Object value) {
        return value != null && value != MissingValue.INSTANCE
                && containerValue(value);
    }

    private static String declaring(String label) {
        RowRuntime.declaredMintLabel(label);
        return label;
    }

    private static String manualMintLabel(String requestedSymbol,
                                  String plannedOccurrenceId,
                                  boolean primitiveRoot) {
        String requested = nonNull(requestedSymbol);
        if (!primitiveRoot) return requested;
        String occurrence = nonNull(plannedOccurrenceId);
        if (requested.isEmpty() || occurrence.isEmpty()) {
            throw new IllegalArgumentException(
                    "manual primitive mint requires symbol and occurrence");
        }
        return requested + ".occ." + Digests.sha256(occurrence);
    }

    private static boolean carriesInputAuthority(
            SymbolizeAction action, JsonElement expression) {
        return action != null && action.declaredSymbolicRoot
                && JavaPrimitiveSmtSemantics.primitive(action.javaType)
                ? VmExpressionIr.carriesSymbolicValue(expression)
                : VmExpressionIr.carriesPropagatedValue(expression);
    }

    private static boolean declaredCommunicationCutPort(
            SymbolizeAction action) {
        return action != null
                && RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT
                .equals(action.sourceKind);
    }
}
