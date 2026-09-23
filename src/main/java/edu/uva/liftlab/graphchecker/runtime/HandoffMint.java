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
 * <p>The producer's expression e_p has just been attached by
 * {@link WireExport}; the element's shadow then becomes a FRESH variable
 * instead, so the consumer's formula has a free variable at the boundary
 * rather than the producer's whole expression inlined into it.  That is
 * what lets the two sides be explored independently and joined offline at
 * H: e_p travels on the row as one member of H's family, never as a
 * substitution.</p>
 *
 * <p>Three entries, one rule.  {@link #mintDelivered} for a delivery whose
 * message carried an element, {@link #mintArrived} for one that carried
 * none -- v_H is the CONSUMER's, so it is minted from what arrived and the
 * row states {@code elementAbsent} -- and {@link #mintAmbient} for a
 * declared port that arrived outside every selected occurrence, because
 * selection decides whose paths are explored and never whether a value
 * crossed.</p>
 *
 * <p>The identity is {@code (port, consumer occurrence, k-th attach of this
 * element, element path)} and nothing else, so the same attach in two
 * replays mints the same variable and an answer written for one is found by
 * the other.  The consumer occurrence is the one the PLAN declares the IN
 * site on, not whichever activation happened to be live when the value
 * arrived.</p>
 */
final class HandoffMint {
    private HandoffMint() {
    }

    /**
     * Files one case-local reference into the VM's own handoff ledger and the
     * exact expression now held by the attached destination.
     */
    static void mintDelivered(CommunicationHandoffSpec site,
                              WireExport.HandoffResult result,
                                             Object owner,
                                             String declaringClass,
                                             String fieldName,
                                             String descriptor,
                                             String producerTaskId,
                                             String producerOccurrenceId) {
        if (site == null) return;
        ActiveRegion active = attachConsumerRegion(site);
        if (active == null) {
            // Same rule on the element-present side: the delivery happened.
            ConcolicRegionRuntime.beginBookkeeping();
            try {
                mintAmbient(site, owner, declaringClass,
                        fieldName, descriptor);
            } finally {
                ConcolicRegionRuntime.endBookkeeping();
            }
            return;
        }
        if (safe(producerTaskId).isEmpty()
                || safe(producerOccurrenceId).isEmpty()) {
            return;
        }
        long exportEvent = result.ok()
                ? optionalLongInteger(result.record, "exportEventId", 0L) : 0L;
        if (exportEvent <= 0L) {
            return;
        }
        // README RPC-1: the reference carries both endpoints of the edge.
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
    static void mintArrived(
            CommunicationHandoffSpec site, Object carrier, String field,
            String descriptor) {
        ConcolicRegionRuntime.beginBookkeeping();
        try {
            ActiveRegion active = attachConsumerRegion(site);
            if (active == null) {
                // The entry rule: the port is declared and the value
                // arrived, so v_H is minted on the ambient activation and
                // the row states the degraded occurrence it arrived in.
                mintAmbient(site, carrier, ConcolicRegionRuntime.CARRIER_CLASS, field,
                        descriptor);
                return;
            }
                mintHandoffVariable(active, site, 0L, 0L, null, "", "", carrier,
                    ConcolicRegionRuntime.CARRIER_CLASS, field, descriptor, true);
        } finally {
            ConcolicRegionRuntime.endBookkeeping();
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
        return site == null ? ConcolicRegionRuntime.activeRegion()
                : ConcolicRegionRuntime.declaringRegion(new ConcolicRegionRuntime.Declares.Port(safe(site.portId())));
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
        List<HandoffLeaf> leaves = handoffLeaves(portId, owner, element);
        if (leaves.isEmpty()) {
            // Never silence: a port whose delivered value exposes no
            // primitive leaf the VM can mint on has no v_H, and a row
            // without one names no occurrence two replays could be joined
            // at, so the loss is named -- in the same words the ambient
            // sibling uses, so one fact is stated once.
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC, portId,
                    "the delivered element exposes no primitive leaf to mint"
                            + " a boundary variable on");
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
        // k is the OCCURRENCE's count (I3: ordinals belong to the performer),
        // not the activation's: every element of one message converted in a
        // call of its own is an activation of its own, all folding into one
        // occurrence, and a per-activation k restarted at 1 for each.
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
            // The endpoint first: an obligation answers an attach BY its
            // endpoint id (INTERACTION-ID), so the consumer endpoint has to
            // be named before the answer is written into the leaf.
            edu.uva.liftlab.graphchecker.contract.Endpoint consumer =
                    RowRuntime.nextEndpoint(active.d3Address, portId,
                            WireExport.attemptOf(
                                    RuntimeTraceContext.current()));
            String answer = consumer == null ? ""
                    : edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                            .answer(consumer.id());
            if (!answer.isEmpty() && !RootMint.writeModeledField(owner, signature,
                    descriptor, answer)) {
                // The obligation's answer for this H was not written, so
                // this replay ran the value that arrived where the wave
                // asked for another one.  The same refusal a root mint
                // states (#applyFocusedRootAssignment), by name, instead of
                // an exception the catch below would have flattened into
                // "the mint failed".
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

    /**
     * The identity this attach mints v_H under, and the key an obligation's
     * answer for it is looked up by.
     *
     * <p>{@code (port, consumer occurrence, k-th attach of this element,
     * element path)} and nothing else, so the same attach in two replays
     * mints the same variable and an answer written for one is found by the
     * other.  Empty when any part is missing, which is an attach no replay
     * could be joined at.</p>
     *
     * <p>// D2: keyed by the consumer Endpoint and published as an AttachRow
     * by SessionPublisher (M2).</p>
     */
    private static final String HANDOFF_MINT_PREFIX = "HANDOFF_PHASE.";

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
     * The label the VM mints v_H under.
     *
     * <p>Deliberately not the configured source's {@code SRC.} label: a
     * handoff root and a configured-source root are told apart by name
     * alone, because the importer recognises a configured-source mint by the
     * {@code _field_SRC.<label>_} marker inside the root it reads back.</p>
     */
    static String mintLabel(String mintKey, String portId) {
        return "HOFF." + ArtifactIO.sha256(mintKey + "\n"
                + safe(portId));
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
        ActiveRegion declaring = ConcolicRegionRuntime.declaringRegion(new ConcolicRegionRuntime.Declares.Port(portId));
        // None live declares it: the attach is where it is, and the row
        // says so rather than borrowing another occurrence's address.  A
        // CALL_RETURN attach whose callee has already closed and published
        // lands here, and R5 then reports it against the carrier.
        return declaring == null ? carrying.activation.occurrenceId
                : declaring.activation.occurrenceId;
    }

    /**
     * States one delivered v_H as the consumer endpoint of an interaction.
     *
     * <p>The row carries both endpoints: this consumer, and the producer
     * the run paired it with -- by the VM handle the producer staged, which
     * is the pairing evidence the run itself recorded.  A delivery nothing
     * paired says so rather than naming a producer it guessed.</p>
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
            // The same rule as the export side: the delivery happened, and
            // a consumer endpoint nothing published is a handoff no arm can
            // be keyed by.
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC, portId,
                    "this delivery published no consumer endpoint row, so no"
                            + " arm can be keyed by it: "
                            + ConcolicRegionRuntime.rootCause(unstated));
        }
    }

    /**
     * Mints v_H at a declared port that arrived outside every selected
     * occurrence -- the entry rule.
     *
     * <p>Every declared port mints on arrival, whatever is selected: the
     * value crossed the boundary and the consumer's formula needs a free
     * variable there, and which occurrence it happened in is what the row
     * says about itself rather than a condition on saying it.  Selection
     * decides only whose paths are explored (REPORT-ENTRY §2).  Path
     * recording is deliberately NOT started: an unselected activation
     * records no path, which is precisely what not selecting it means.</p>
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

    /**
     * The attaches of each element so far at each consumer occurrence, by
     * {@code (occurrence, port, element path)}: k of a handoff's identity,
     * selected or ambient.  Guarded by itself.
     */
    private static final Map<String, Integer> ATTACHES =
            new HashMap<String, Integer>();

    /**
     * k for the next attach of one element at one consumer occurrence.
     *
     * <p>Counted per OCCURRENCE, as every ordinal a row carries is (I3): a
     * count kept on the activation restarts in each activation that folds
     * into the occurrence.  hdfs-17967 path A, after the ambient fix: the
     * mirror's heartbeat delivered four block keys, each converted by a
     * {@code convert(BlockKeyProto)} activation of its own, and each
     * activation counted its attach as the first -- four keys, one symbol.</p>
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
     * The identity an ambient attach mints v_H under: THE SAME
     * {@code (port, consumer occurrence, k-th attach of this element,
     * element path)} a selected attach is keyed by, k counted by
     * {@link #nextAttach} for both.
     *
     * <p>k was the constant 1, so every element one occurrence received on
     * one port was ONE variable.  hdfs-17899 bug1: target-dn's heartbeat
     * delivered four block keys, 119979, 119978, 119981 and 119980, one
     * {@code convert(BlockKeyProto)} each, each paired to its own producer
     * on the NameNode -- and all four arrived on one symbol, so the formula
     * put every key under one key id and never put back the key the clock
     * move had just expired.  The witness that followed moved a DataNode
     * clock the real program would have survived: the review of the v9
     * passes rejected bug1 and 17967 A, B and C on it.</p>
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
     * The primitive leaves one attach delivered.
     *
     * <p>A primitive destination is one leaf, itself.  A reference or array
     * destination is the leaves reachable through it that the VM can mint
     * on: each element's declared primitive instance fields, index-qualified
     * so two elements are two handoff occurrences.  An array of primitives
     * has no field to address and yields none, which the caller names rather
     * than passes over.</p>
     *
     * <p>The cap is named too.  A leaf above it is a boundary variable the
     * run never minted, so no later stage can join that half of the
     * delivery at all -- and an unnamed cap reads from the corpus exactly
     * like a delivery that carried nothing there.  The row states the port,
     * the cap, and what was left out, counted exactly and without a second
     * walk: the delivered array elements never visited, and the declared
     * primitive fields of the elements that were.</p>
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
        // Only the application's own objects.  An array of primitives boxes
        // each element on the way out of reflection, and java.lang.Integer's
        // own private "value" is not a leaf the workload addresses -- it is
        // the box the array element already is, and minting into it would
        // publish a handoff at a field no decode ever reads.
        if (owner.getClass().getName().startsWith("java.")) return 0;
        int dropped = 0;
        for (Field field : owner.getClass().getDeclaredFields()) {
            if (java.lang.reflect.Modifier.isStatic(field.getModifiers())
                    || !field.getType().isPrimitive()) {
                continue;
            }
            if (leaves.size() >= HANDOFF_LEAF_LIMIT) {
                // Counted, not minted: the caller names how many.
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
