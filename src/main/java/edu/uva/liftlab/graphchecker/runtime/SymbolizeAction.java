package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;

import com.google.gson.JsonElement;

import com.google.gson.JsonObject;

import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.smt.CanonicalJson;

import edu.uva.liftlab.graphchecker.plan.FieldPathSpec;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveBoxing;

import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.instanceOfName;

import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.resolveFieldPathLeafOwner;

import edu.uva.liftlab.graphchecker.plan.SiteId;

import java.util.ArrayList;

import java.util.Collections;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;

import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

final class SymbolizeAction {
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
    /** How the finalizer classified the port that minted this action. */
    final String sourceKind;
    /** A clock input's clock (the plan's: the JVM clock it wraps, its
     *  tick), null for any other input. */
    final Clock clock;
    /** A configuration getter's return: the root it is ({@code
     *  CONFIG:<key>}) and its static domain; "" for any other input. */
    final String configSource;
    final String configDomainMin;
    final String configDomainMax;
    /** A fault marker's name ({@code FAULT:<TRANSPORT>:..}); "" for any
     *  other input. */
    final String marker;
    /** The static site the plan observed this read at, or "". */
    final String siteId;
    /** The recorded event this read was observed at, or -1. */
    final long eventSeq;
    /** What this read returned in the recording, or "" when unobserved. */
    final String recordedPrimitiveValue;
    /** The selection file named this input by hand: mint, do not reuse. */
    final boolean declaredSymbolicRoot;
    final List<String> fieldPath;
    final String javaType;
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
        this.method = optionalString(json, "method");
        this.local = optionalString(json, "local");
        int unitIndex = optionalInteger(json, "unitIndex", -1);
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
        this.sourceKind = optionalString(json, "sourceKind");
        long clockNanos = optionalLongInteger(json,
                InputActionCatalog.DECLARED_WALL_CLOCK, 0L);
        this.clock = clockNanos > 0L ? Clock.of(clockNanos, optionalString(
                json, InputActionCatalog.DECLARED_CLOCK_SOURCE)) : null;
        this.configSource = optionalString(json,
                InputActionCatalog.DECLARED_CONFIG_SOURCE);
        this.configDomainMin = optionalString(json,
                InputActionCatalog.DECLARED_DOMAIN_MIN);
        this.configDomainMax = optionalString(json,
                InputActionCatalog.DECLARED_DOMAIN_MAX);
        this.marker = optionalString(json,
                InputActionCatalog.DECLARED_FAULT_MARKER);
        this.siteId = optionalString(json, "siteId");
        this.eventSeq = optionalLongInteger(json, "eventSeq", -1L);
        this.recordedPrimitiveValue = optionalBool(json, "observed", false)
                ? optionalString(json, "primitiveValue") : "";
        this.declaredSymbolicRoot = optionalBool(json,
                InputActionCatalog.DECLARED_SYMBOLIC_ROOT, false);
        String explicitLeafSignature = firstNonBlank(
                optionalString(json, "leafFieldSignature"),
                this.accessFieldSignature);
        this.fieldPaths = new ArrayList<>(
                FieldPathSpec.paths(json, "fieldPaths"));
        if (this.fieldPaths.isEmpty() && !this.fieldPath.isEmpty()) {
            this.fieldPaths.add(new ArrayList<>(this.fieldPath));
        }
        // One declared field per hop of a multi-hop port.
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

    /** A root-argument action, whole or by field path, at this index. */
    boolean atArgument(int argumentIndex) {
        return index == argumentIndex && ("ARGUMENT".equals(location)
                || "ARGUMENT_FIELD_PATH".equals(location));
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
        return accessorConstrained() || acceptsOccurrence(actualOccurrence);
    }

    /** The action names an accessor call: its reads are that call's. */
    private boolean accessorConstrained() {
        return !accessorCallerMethod.isEmpty()
                || accessorCallUnitIndex >= 0
                || !accessorDeclaredCallee.isEmpty()
                || !accessorImplementationMethod.isEmpty();
    }

    boolean repeatedPrimitiveAccessor() {
        return "LOCAL_DEFINITION".equals(bindingMode)
                && "CALL_RETURN".equals(location)
                && JavaPrimitiveBoxing.unboxReturn(cell);
    }

    /** A declared wall-clock read with a recorded answer (moved by offset). */
    boolean declaresWallClockRead() {
        return clock != null && !recordedPrimitiveValue.isEmpty();
    }

    /** Where this input's value enters the world, as its mint states it:
     *  a clock's reading, a configuration, a fault marker, else a read. */
    RootCategory category() {
        if (declaresWallClockRead()) return RootCategory.CLOCK;
        if (!configSource.isEmpty()) return RootCategory.CONFIG;
        return RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT.equals(
                sourceKind) ? RootCategory.FAULT : RootCategory.READ;
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

    /** The logical path for an exact getstatic materialization. */
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
                                 String signature, String actualField) {
        if (!("FIELD_ACCESS".equals(bindingMode)
                || "HEAP_OBJECT_FIELD".equals(location))) {
            return false;
        }
        boolean accessorConstrained = accessorConstrained();
        String accessorSiteId = accessorCallerMethod.isEmpty()
                || accessorCallUnitIndex < 0 ? ""
                : SiteId.render(accessorCallerMethod,
                        accessorCallUnitIndex);
        boolean accessSiteConstrained = !accessSites.isEmpty();
        // Accessor actions name the caller's invoke site, not this read.
        if (accessSiteConstrained) {
            String constrainedSite = accessorConstrained
                    ? accessorSiteId
                    : SiteId.render(actualMethod, actualUnitIndex);
            if (constrainedSite.isEmpty()
                    || !accessSites.contains(constrainedSite)) {
                return false;
            }
        }
        Boolean lightweightContext = ConcolicRegionRuntime
                .lightweightAccessorContextMatches(
                accessorCallerMethod, accessorCallUnitIndex,
                accessorSiteId, accessorDeclaredCallee, owner);
        boolean accessorContextMatches = lightweightContext != null
                ? lightweightContext
                : CausynthTraceRecorder.currentCallParentSiteMatches(
                accessorCallerMethod, accessorCallUnitIndex,
                accessorSiteId, accessorDeclaredCallee);
        int actualAccessorOccurrence =
                ConcolicRegionRuntime.lightweightAccessorContextOccurrence();
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
        // A path rooted at a return/local may have no static owner.
        return !accessOwnerClass.isEmpty()
                || !safe(signature).isEmpty()
                && cell.contains(safe(signature));
    }

    Object leafOwner(Object accessOwner) {
        return resolveFieldPathLeafOwner(accessOwner, fieldPath);
    }

    /** The exact declaration of the leaf that will be symbolized. */
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
