package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.declaredInstanceField;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.exactFieldSignature;
import static edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.lang.reflect.Field;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.UUID;

/**
 * R4's far half: v_H, the consumer's boundary variable, minted on the value
 * that arrived.
 *
 * <p>After {@link WireExport} attaches the producer's e_p, the element's
 * shadow becomes a FRESH variable, so the two sides are explored
 * independently and joined offline at H; e_p travels on the row, never as a
 * substitution.  Entries: {@link #mintDelivered} (element carried),
 * {@link #mintArrived} (none; row states {@code elementAbsent}) and
 * {@link #mintAmbient} (outside every selected occurrence -- selection
 * decides whose paths are explored, never whether a value crossed).</p>
 *
 * <p>Identity is {@code (port, consumer occurrence, k-th attach, element
 * path)} only, so the same attach in two replays mints the same variable.
 * The consumer occurrence is the one the PLAN declares the IN site on, not
 * the live one.</p>
 */
final class HandoffMint {
    private HandoffMint() {
    }

    /** Mints v_H for a delivery whose message carried an element. */
    static void mintDelivered(CommunicationHandoffSpec site,
                              WireExport.HandoffResult result,
                                             Object owner,
                                             String declaringClass,
                                             String fieldName,
                                             String descriptor) {
        if (site == null) return;
        ActiveRegion active = attachConsumerRegion(site);
        if (active == null) {
            ConcolicRegionRuntime.beginBookkeeping();
            try {
                mintAmbient(site, owner, declaringClass,
                        fieldName, descriptor);
            } finally {
                ConcolicRegionRuntime.endBookkeeping();
            }
            return;
        }
        long exportEvent = result.ok()
                ? optionalLongInteger(result.record, "exportEventId", 0L) : 0L;
        if (exportEvent <= 0L) {
            return;
        }
        // README RPC-1: both endpoints of the edge.
        long attachEvent = result.ok()
                ? optionalLongInteger(result.record, "attachEventId", 0L) : 0L;
        if (attachEvent <= 0L) {
            return;
        }
        JsonElement expression;
        try {
            Field storage = declaredInstanceField(owner, declaringClass,
                    fieldName, descriptor);
            if (storage == null) {
                return;
            }
            Object value = storage.get(owner);
            ConcolicVmBroker api = engine();
            expression = RootMint.containerValue(value)
                    ? ConcolicRegionRuntime.engineExpression(api.expression(value))
                    : ConcolicRegionRuntime.engineExpression(api.fieldExpression(owner,
                    declaringClass, fieldName, descriptor, value));
        } catch (Throwable failure) {
            return;
        }
        if (expression == null || expression.isJsonNull()) {
            return;
        }
        Interactions.deliveringAt(attachEvent);
        mintHandoffVariable(active, site, exportEvent, attachEvent,
                expression, owner, declaringClass, fieldName, descriptor,
                false);
    }

    /**
     * Mints v_H at a declared capture whose message carried no element: the
     * row states {@code elementAbsent} and no producer; an answer is written
     * on the carrier leaf as usual.
     */
    static void mintArrived(
            CommunicationHandoffSpec site, Object carrier, String field,
            String descriptor) {
        ConcolicRegionRuntime.beginBookkeeping();
        try {
            ActiveRegion active = attachConsumerRegion(site);
            if (active == null) {
                mintAmbient(site, carrier, ConcolicRegionRuntime.CARRIER_CLASS, field,
                        descriptor);
                return;
            }
                mintHandoffVariable(active, site, 0L, 0L, null, carrier,
                    ConcolicRegionRuntime.CARRIER_CLASS, field, descriptor, true);
        } finally {
            ConcolicRegionRuntime.endBookkeeping();
        }
    }

    /**
     * The activation this attach belongs to: the innermost live region whose
     * plan declares this port IN.  Trap: the innermost live region may not
     * own the site, and filing there reports one attach twice.  When none
     * declares it the innermost live one carries the row, and R5 reports it
     * unplanned; null only when no region is live.
     */
    private static ActiveRegion attachConsumerRegion(
            CommunicationHandoffSpec site) {
        return site == null ? ConcolicRegionRuntime.activeRegion()
                : ConcolicRegionRuntime.declaringRegion(new ConcolicRegionRuntime.Declares.Port(safe(site.portId())));
    }

    /**
     * Mints v_H on each primitive leaf this attach landed on: one variable per
     * handoff occurrence (k is part of H), by the configured-source mint
     * mechanism under a handoff label.
     */
    private static void mintHandoffVariable(
            ActiveRegion active, CommunicationHandoffSpec site,
            long exportEvent, long attachEvent, JsonElement producerExpression,
            Object owner, String declaringClass, String fieldName,
            String descriptor, boolean elementAbsent) {
        String portId = safe(site.portId());
        Field element = declaredInstanceField(owner, declaringClass,
                fieldName, descriptor);
        List<HandoffLeaf> leaves = handoffLeaves(portId, owner, element);
        if (leaves.isEmpty()) {
            // No leaf, no v_H: name the loss (same words as mintAmbient).
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC, portId,
                    "the delivered element exposes no primitive leaf to mint"
                            + " a boundary variable on");
            return;
        }
        for (HandoffLeaf leaf : leaves) {
            mintHandoffLeaf(active, portId, exportEvent, attachEvent,
                    producerExpression, leaf, elementAbsent);
        }
    }

    /**
     * Mints v_H at one primitive leaf of one attach.  A reference or array
     * port is one attach and several variables (e.g. {@code [i].keyId}), each
     * its own handoff occurrence for R3.
     */
    private static void mintHandoffLeaf(
            ActiveRegion active, String portId, long exportEvent,
            long attachEvent, JsonElement producerExpression,
            HandoffLeaf leaf, boolean elementAbsent) {
        String elementPath = leaf.path;
        // H belongs to the declared IN occurrence, not the live one (a
        // CALL_RETURN attach runs in the caller's frame).
        String consumerOccurrenceId = declaredConsumerOccurrence(portId,
                active);
        // k is the OCCURRENCE's count (I3), not the activation's.
        String phaseId = handoffMintKey(portId,
                consumerOccurrenceId,
                nextAttach(consumerOccurrenceId, portId, elementPath),
                elementPath);
        if (phaseId.isEmpty()) return;
        Object owner = leaf.owner;
        Field element = leaf.field;
        String declaringClass = element.getDeclaringClass().getName();
        String fieldName = element.getName();
        String descriptor = javaTypeDescriptor(
                element.getType().getTypeName());
        try {
            ConcolicVmBroker api = engine();
            String recordedValue = ConcolicRegionRuntime.recordedScalar(element.get(owner));
            // Identity is the indexed path; the VM resolves the bare
            // field signature.
            String signature = leaf.signature();
            // Name the endpoint first: an obligation answers an attach by
            // its endpoint id (INTERACTION-ID).
            edu.uva.liftlab.graphchecker.contract.Endpoint consumer =
                    RowRuntime.nextEndpoint(active.d3Address, portId,
                            WireExport.attemptOf(
                                    RuntimeTraceContext.current()));
            String answer = consumer == null ? ""
                    : edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                            .answer(consumer.id());
            if (!answer.isEmpty() && !RootMint.writeModeledField(owner, signature,
                    descriptor, answer)) {
                // The answer was not written: the same named refusal a
                // root mint states (#applyFocusedRootAssignment).
                RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.ASSIGNMENT_UNPLANTED,
                        edu.uva.liftlab.graphchecker.contract.GapClass.BLOCKING, portId,
                        "the wave's answer for this handoff could not be"
                                + " written into " + signature);
                return;
            }
            api.symbolizeExactField(owner, signature,
                    mintLabel(phaseId, portId));
            ConcolicRegionRuntime.ensurePathRecordingStarted(active);
            JsonObject minted = exactSymbolOf(ConcolicRegionRuntime.engineExpression(
                    api.fieldExpression(owner, declaringClass, fieldName,
                            descriptor, element.get(owner))));
            if (minted == null) {
                return;
            }
            publishAttachRow(consumer, portId,
                    optionalString(minted, "_exp"),
                    optionalString(minted, "_java_type"), recordedValue,
                    !answer.isEmpty(), answer);
        } catch (Throwable failure) {
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC, portId,
                    "the boundary variable of this attach was not minted, so"
                            + " the delivery names no occurrence two replays"
                            + " could be joined at: " + ConcolicRegionRuntime.rootCause(failure));
        }
    }

    private static final String HANDOFF_MINT_PREFIX = "HANDOFF_PHASE.";

    /**
     * The identity v_H is minted under and its answer looked up by:
     * {@code (port, consumer occurrence, k, element path)}; empty when any
     * part is missing.
     */
    private static String handoffMintKey(String portId,
                                         String consumerAddress,
                                         int attachOrdinal,
                                         String elementPath) {
        if (safe(portId).isEmpty() || safe(consumerAddress).isEmpty()
                || safe(elementPath).isEmpty() || attachOrdinal < 1) {
            return "";
        }
        String identity = portId + "\n" + consumerAddress + "\n"
                + attachOrdinal + "\n" + elementPath;
        return HANDOFF_MINT_PREFIX + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8));
    }

    /**
     * The label the VM mints v_H under.  Never {@code SRC.}: the importer
     * tells a configured-source root by its {@code _field_SRC.<label>_}
     * marker.
     */
    static String mintLabel(String mintKey, String portId) {
        return "HOFF." + ArtifactIO.sha256(mintKey + "\n"
                + safe(portId));
    }

    /**
     * The occurrence this port's IN site is declared on (stable across
     * replays), else the carrying activation -- R5's UNPLANNED_HANDOFF.
     */
    private static String declaredConsumerOccurrence(String portId,
                                                     ActiveRegion carrying) {
        // The LIVE declaring activation, not the first declaring task in
        // the plan: several occurrences may declare one port.
        ActiveRegion declaring = ConcolicRegionRuntime.declaringRegion(new ConcolicRegionRuntime.Declares.Port(portId));
        return declaring == null ? carrying.activation.occurrenceId
                : declaring.activation.occurrenceId;
    }

    /**
     * States one delivered v_H as the consumer endpoint of an interaction,
     * paired to its producer by the staged VM handle, never by a guess.
     */
    private static void publishAttachRow(
            edu.uva.liftlab.graphchecker.contract.Endpoint consumer,
            String portId, String symbol, String javaType, String arrival,
            boolean answered, String answeredValue) {
        if (consumer == null || !RowRuntime.open()) return;
        try {
            RuntimeTraceContext.View view = RuntimeTraceContext.current();
            RowRuntime.attachedAt(consumer, Interactions.deliverySeq(), portId,
                    Interactions.deliveryHandle(),
                    view.exchangeCorrelationId, symbol, javaType, arrival,
                    answered, answeredValue);
        } catch (Throwable unstated) {
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC, portId,
                    "this delivery published no consumer endpoint row, so no"
                            + " arm can be keyed by it: "
                            + ConcolicRegionRuntime.rootCause(unstated));
        }
    }

    /**
     * Mints v_H at a declared port that arrived outside every selected
     * occurrence (the entry rule, REPORT-ENTRY §2).  Path recording is
     * deliberately NOT started: an unselected activation records no path.
     */
    private static void mintAmbient(
            CommunicationHandoffSpec site, Object owner,
            String declaringClass, String fieldName, String descriptor) {
        String portId = safe(site.portId());
        if (!RowRuntime.open()) return;
        RuntimeTraceContext.View view = RuntimeTraceContext.current();
        edu.uva.liftlab.graphchecker.contract.OccurrenceAddress consumer =
                RowRuntime.occurrenceHere(view.source == null ? ""
                        : view.source.key(), portId);
        if (consumer == null) {
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                            .LINEAGE_LOST,
                    edu.uva.liftlab.graphchecker.contract.GapClass
                            .BLOCKING, portId,
                    "a declared port arrived on a thread naming no node, so"
                            + " the delivery has no consumer address");
            return;
        }
        RowRuntime.ambientActivation(consumer);
        Field element = declaredInstanceField(owner, declaringClass,
                fieldName, descriptor);
        List<HandoffLeaf> leaves = handoffLeaves(portId, owner, element);
        if (leaves.isEmpty()) {
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                            .UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass
                            .DIAGNOSTIC, portId,
                    "the delivered element exposes no primitive leaf to mint"
                            + " a boundary variable on");
            return;
        }
        for (HandoffLeaf leaf : leaves) {
            try {
                ConcolicVmBroker api = engine();
                Field field = leaf.field;
                String recordedValue = ConcolicRegionRuntime.recordedScalar(field.get(leaf.owner));
                String mintKey = ambientMintKey(portId, consumer.render(),
                        leaf.path);
                api.symbolizeExactField(leaf.owner, leaf.signature(),
                        mintLabel(mintKey, portId));
                JsonObject minted = exactSymbolOf(ConcolicRegionRuntime.engineExpression(
                        api.fieldExpression(leaf.owner,
                                field.getDeclaringClass().getName(),
                                field.getName(), javaTypeDescriptor(
                                        field.getType().getTypeName()),
                                field.get(leaf.owner))));
                publishAttachRow(RowRuntime.nextEndpoint(consumer, portId,
                                WireExport.attemptOf(view)), portId,
                        minted == null ? "" : optionalString(minted, "_exp"),
                        minted == null ? ""
                                : optionalString(minted, "_java_type"),
                        recordedValue, false, "");
            } catch (Throwable failure) {
                RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                                .UNSTATED_VALUE,
                        edu.uva.liftlab.graphchecker.contract.GapClass
                                .DIAGNOSTIC, portId,
                        "the entry-rule mint failed at " + portId + ": "
                                + ConcolicRegionRuntime.rootCause(failure));
            }
        }
    }

    /** k per {@code (occurrence, port, element path)}.  Guarded by itself. */
    private static final Map<String, Integer> ATTACHES =
            new HashMap<String, Integer>();

    /**
     * k for the next attach of one element at one consumer occurrence.
     * Counted per OCCURRENCE (I3): a per-activation count restarts in each
     * activation folding into it, merging distinct elements into one symbol.
     */
    static int nextAttach(String consumer, String portId,
                          String elementPath) {
        String element = safe(consumer) + "\n" + safe(portId) + "\n"
                + safe(elementPath);
        synchronized (ATTACHES) {
            Integer previous = ATTACHES.get(element);
            int ordinal = previous == null ? 1 : previous + 1;
            ATTACHES.put(element, ordinal);
            return ordinal;
        }
    }

    /**
     * The identity an ambient attach mints v_H under: the same key a selected
     * attach uses, k from {@link #nextAttach}.  Trap: a constant k makes every
     * element on one port one variable.
     */
    static String ambientMintKey(String portId, String consumer,
                                 String elementPath) {
        return handoffMintKey(portId, consumer,
                nextAttach(consumer, portId, elementPath), elementPath);
    }

    static void resetForTests() {
        synchronized (ATTACHES) {
            ATTACHES.clear();
        }
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
     * The primitive leaves one attach delivered: the field itself if
     * primitive, else each element's declared primitive instance fields,
     * index-qualified.  An array of primitives yields none.  Hitting the cap
     * is named as a gap, since an unminted leaf is otherwise indistinguishable
     * from nothing delivered.
     */
    private static List<HandoffLeaf> handoffLeaves(String portId,
                                                   Object owner,
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
        int droppedFields = 0;
        if (value.getClass().isArray()) {
            int length = java.lang.reflect.Array.getLength(value);
            int index = 0;
            for (; index < length
                    && leaves.size() < HANDOFF_LEAF_LIMIT; index++) {
                Object item = java.lang.reflect.Array.get(value, index);
                if (item == null) continue;
                droppedFields += addPrimitiveLeaves(item, "[" + index + "]",
                        leaves);
            }
            noteTruncatedHandoff(portId, leaves.size(), length - index,
                    droppedFields);
            return leaves;
        }
        droppedFields = addPrimitiveLeaves(value, "", leaves);
        noteTruncatedHandoff(portId, leaves.size(), 0, droppedFields);
        return leaves;
    }

    /** Names one delivery whose boundary variables did not fit the cap. */
    private static void noteTruncatedHandoff(String portId, int minted,
                                             int droppedElements,
                                             int droppedFields) {
        if (droppedElements <= 0 && droppedFields <= 0) return;
        RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.BOUND_INSUFFICIENT,
                edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC, portId,
                "this delivery minted " + minted + " boundary variable(s)"
                        + " and stopped at the " + HANDOFF_LEAF_LIMIT
                        + "-leaf cap, leaving " + droppedElements
                        + " delivered element(s) and " + droppedFields
                        + " declared primitive field(s) with none, so no"
                        + " later stage can join a handoff at them");
    }

    /** @return how many qualifying leaves the cap left out */
    private static int addPrimitiveLeaves(Object owner, String prefix,
                                          List<HandoffLeaf> leaves) {
        // Only application objects: a boxed primitive's "value" is a field
        // no decode reads.
        if (owner.getClass().getName().startsWith("java.")) return 0;
        int dropped = 0;
        for (Field field : owner.getClass().getDeclaredFields()) {
            if (java.lang.reflect.Modifier.isStatic(field.getModifiers())
                    || !field.getType().isPrimitive()) {
                continue;
            }
            if (leaves.size() >= HANDOFF_LEAF_LIMIT) {
                dropped++;
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
        return dropped;
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
}
