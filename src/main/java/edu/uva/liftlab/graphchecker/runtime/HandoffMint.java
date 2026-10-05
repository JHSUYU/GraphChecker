package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.CARRIER_CLASS;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.pauseObservation;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.resumeObservation;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.declaredInstanceField;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.exactFieldSignature;
import static edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;

import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.UUID;

/**
 * The wire's far half (SYMBOL-SCOPE §6.3): v_H, the consumer's boundary
 * variable, minted on the value that arrived.
 *
 * <p>After {@link WireExport} attaches the producer's e_p, the element's
 * shadow becomes a FRESH variable, so the two sides are explored
 * independently and joined offline at H; e_p travels on the row, never as a
 * substitution.  Entries: {@link #mintDelivered} (element carried),
 * {@link #mintArrived} (none carried) and
 * {@link #mintAmbient} (outside every selected occurrence -- selection
 * decides whose paths are explored, never whether a value crossed).</p>
 *
 * <p>Identity is {@code (port, consumer occurrence, k-th attach, element
 * path)} only, so the same attach in two replays mints the same variable.
 * For a {@code WIRE_FLOW} port the consumer occurrence is the one the PLAN
 * declares the IN site on, not the live one, and the attached leaf is a
 * field of the carrier ({@link ConcolicRegionRuntime#CARRIER_CLASS}).</p>
 */
final class HandoffMint {
    private HandoffMint() {
    }

    /**
     * Mints v_H for a delivery whose message carried an element, attached at
     * VM event {@code attachEventId}.  Runs with observation paused.
     */
    static void mintDelivered(CommunicationHandoffSpec site,
                              long attachEventId, Object carrier,
                              String field, String descriptor) {
        ActiveRegion active = attachConsumerRegion(site);
        if (active == null) {
            mintAmbient(site, carrier, field, descriptor);
            return;
        }
        // Only an element the VM states an expression for is minted on.
        String unstated;
        try {
            Field storage = declaredInstanceField(carrier, CARRIER_CLASS,
                    field, descriptor);
            JsonElement expression = storage == null ? null
                    : RootMint.cellExpression(engine(), carrier,
                    CARRIER_CLASS, field, descriptor, storage.get(carrier));
            unstated = expression == null || expression.isJsonNull()
                    ? "the VM states no expression for the attached leaf"
                    : "";
        } catch (Throwable failure) {
            unstated = ConcolicRegionRuntime.rootCause(failure);
        }
        if (!unstated.isEmpty()) {
            unminted(active, site.portId(), unstated);
            return;
        }
        Interactions.deliveringAt(attachEventId);
        mintHandoffVariable(active, site, carrier, field, descriptor);
    }

    /**
     * Mints v_H at a declared capture whose message carried no element; an
     * answer is written on the carrier leaf as usual.
     */
    static void mintArrived(
            CommunicationHandoffSpec site, Object carrier, String field,
            String descriptor) {
        pauseObservation();
        try {
            ActiveRegion active = attachConsumerRegion(site);
            if (active == null) {
                mintAmbient(site, carrier, field, descriptor);
                return;
            }
            mintHandoffVariable(active, site, carrier, field, descriptor);
        } finally {
            resumeObservation();
        }
    }

    /**
     * The activation this attach belongs to: the innermost live region whose
     * plan declares this port IN (stable across replays).  Trap: the
     * innermost live region may not own the site, and filing there reports
     * one attach twice.  When none declares it the innermost live one
     * carries the row, reported unplanned (UNPLANNED_HANDOFF); null
     * only when no region is live.
     */
    private static ActiveRegion attachConsumerRegion(
            CommunicationHandoffSpec site) {
        return ConcolicRegionRuntime.declaringRegion(
                new ConcolicRegionRuntime.Declares.Port(safe(site.portId())));
    }

    /**
     * Mints v_H on each primitive leaf this attach landed on: one variable per
     * handoff occurrence (k is part of H), by the configured-source mint
     * mechanism under a handoff label.
     */
    private static void mintHandoffVariable(
            ActiveRegion active, CommunicationHandoffSpec site,
            Object carrier, String field, String descriptor) {
        String portId = safe(site.portId());
        for (HandoffLeaf leaf : handoffLeaves(portId, carrier, field,
                descriptor)) {
            mintHandoffLeaf(active, portId, leaf);
        }
    }

    /**
     * Mints v_H at one primitive leaf of one attach.  A reference or array
     * port is one attach and several variables (e.g. {@code [i].keyId}), each
     * its own handoff occurrence.
     */
    private static void mintHandoffLeaf(ActiveRegion active, String portId,
                                        HandoffLeaf leaf) {
        // H belongs to the declared IN occurrence (#attachConsumerRegion),
        // not the live one: a CALL_RETURN attach runs in the caller's frame.
        // k is the OCCURRENCE's count (I3), not the activation's.
        String consumerOccurrenceId = active.activation.occurrenceId;
        String phaseId = handoffMintKey(portId, consumerOccurrenceId,
                nextAttach(consumerOccurrenceId, portId, leaf.path),
                leaf.path);
        if (phaseId.isEmpty()) {
            unminted(active, portId, "its identity names no consumer"
                    + " occurrence or element path");
            return;
        }
        String descriptor = javaTypeDescriptor(
                leaf.field.getType().getTypeName());
        try {
            String recordedValue = ConcolicRegionRuntime.recordedScalar(
                    leaf.field.get(leaf.owner));
            // Name the endpoint first: an obligation answers an attach by
            // its endpoint id (CONTRACT-SPEC §3).
            Endpoint consumer = RowRuntime.nextEndpoint(active.d3Address,
                    portId, WireExport.attemptOf(
                            RuntimeTraceContext.current()));
            String answer = consumer == null ? ""
                    : FocusedReplay.answer(consumer.id());
            // Identity is the indexed path; the VM resolves the bare
            // field signature.
            if (!answer.isEmpty() && !RootMint.writeModeledField(leaf.owner,
                    leaf.signature(), descriptor, answer)) {
                // The answer was not written: the same named refusal a
                // root mint states (#applyFocusedRootAssignment).
                RowRuntime.gap(GapKind.ASSIGNMENT_UNPLANTED,
                        GapClass.BLOCKING, portId,
                        "the wave's answer for this handoff could not be"
                                + " written into " + leaf.signature());
                return;
            }
            JsonObject minted = mintLeaf(active, leaf,
                    mintLabel(phaseId, portId));
            if (minted == null) {
                unminted(active, portId, "the VM read " + leaf.path
                        + " back as no one exact symbol");
                return;
            }
            publishAttachRow(consumer, portId,
                    optionalString(minted, "_exp"),
                    optionalString(minted, "_java_type"), recordedValue,
                    answer);
        } catch (Throwable failure) {
            unminted(active, portId, ConcolicRegionRuntime.rootCause(failure));
        }
    }

    /**
     * Names one attach inside {@code active} that minted no v_H: the value
     * crossed, but no row keys an arm by it.
     */
    private static void unminted(ActiveRegion active, String portId,
                                 String why) {
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                active.d3Address == null ? portId : active.d3Address.render(),
                "the boundary variable of the attach at " + portId + " was"
                        + " not minted, so the delivery names no occurrence"
                        + " two replays could be joined at: " + why);
    }

    /**
     * Symbolizes one leaf under {@code label} and reads back its exact VM
     * root, or null.  {@code active} opens path recording; an ambient mint
     * (null) records no path.
     */
    private static JsonObject mintLeaf(ActiveRegion active, HandoffLeaf leaf,
                                       String label) throws Exception {
        ConcolicVmBroker api = engine();
        Field field = leaf.field;
        api.symbolizeExactField(leaf.owner, leaf.signature(), label);
        if (active != null) active.pathRecordingStarted = true;
        return exactSymbolOf(ConcolicRegionRuntime.engineExpression(
                api.fieldExpression(leaf.owner,
                        field.getDeclaringClass().getName(), field.getName(),
                        javaTypeDescriptor(field.getType().getTypeName()),
                        field.get(leaf.owner))));
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
    private static String mintLabel(String mintKey, String portId) {
        return "HOFF." + ArtifactIO.sha256(mintKey + "\n"
                + safe(portId));
    }

    /**
     * States one delivered v_H as the consumer endpoint of an interaction,
     * paired to its producer by the staged VM handle, never by a guess.
     * {@code answer} is the wave's value written into it, or "".
     */
    private static void publishAttachRow(Endpoint consumer, String portId,
                                         String symbol, String javaType,
                                         String arrival, String answer) {
        if (consumer == null || !RowRuntime.open()) return;
        try {
            RuntimeTraceContext.View view = RuntimeTraceContext.current();
            RowRuntime.attachedAt(consumer, Interactions.deliverySeq(), portId,
                    Interactions.deliveryHandle(),
                    view.exchangeCorrelationId, symbol, javaType, arrival,
                    !answer.isEmpty(), answer);
        } catch (Throwable unstated) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    portId,
                    "this delivery published no consumer endpoint row, so no"
                            + " arm can be keyed by it: "
                            + ConcolicRegionRuntime.rootCause(unstated));
        }
    }

    /**
     * Mints v_H at a declared port that arrived outside every selected
     * occurrence (the entry rule).  Path recording is
     * deliberately NOT started: an unselected activation records no path.
     */
    private static void mintAmbient(
            CommunicationHandoffSpec site, Object carrier, String field,
            String descriptor) {
        String portId = safe(site.portId());
        if (!RowRuntime.open()) return;
        RuntimeTraceContext.View view = RuntimeTraceContext.current();
        OccurrenceAddress consumer = RowRuntime.occurrenceHere(
                view.source == null ? "" : view.source.key(), portId);
        if (consumer == null) {
            RowRuntime.gap(GapKind.LINEAGE_LOST, GapClass.BLOCKING, portId,
                    "a declared port arrived on a thread naming no node, so"
                            + " the delivery has no consumer address");
            return;
        }
        RowRuntime.ambientActivation(consumer);
        for (HandoffLeaf leaf : handoffLeaves(portId, carrier, field,
                descriptor)) {
            try {
                String recordedValue = ConcolicRegionRuntime.recordedScalar(
                        leaf.field.get(leaf.owner));
                JsonObject minted = mintLeaf(null, leaf, mintLabel(
                        ambientMintKey(portId, consumer.render(), leaf.path),
                        portId));
                publishAttachRow(RowRuntime.nextEndpoint(consumer, portId,
                                WireExport.attemptOf(view)), portId,
                        minted == null ? "" : optionalString(minted, "_exp"),
                        minted == null ? ""
                                : optionalString(minted, "_java_type"),
                        recordedValue, "");
            } catch (Throwable failure) {
                RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        portId,
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
    private static List<HandoffLeaf> handoffLeaves(
            String portId, Object carrier, String field, String descriptor) {
        List<HandoffLeaf> leaves = primitiveLeaves(portId, carrier,
                declaredInstanceField(carrier, CARRIER_CLASS, field,
                        descriptor));
        if (leaves.isEmpty()) {
            // No leaf, no v_H: the loss is named.
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    portId,
                    "the delivered element exposes no primitive leaf to mint"
                            + " a boundary variable on");
        }
        return leaves;
    }

    private static List<HandoffLeaf> primitiveLeaves(String portId,
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
            int length = Array.getLength(value);
            int index = 0;
            for (; index < length
                    && leaves.size() < HANDOFF_LEAF_LIMIT; index++) {
                Object item = Array.get(value, index);
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
        RowRuntime.gap(GapKind.BOUND_INSUFFICIENT, GapClass.DIAGNOSTIC,
                portId,
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
            if (Modifier.isStatic(field.getModifiers())
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
