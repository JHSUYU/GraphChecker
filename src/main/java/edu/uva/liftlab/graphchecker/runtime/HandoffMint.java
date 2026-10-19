package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;
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

final class HandoffMint {
    private HandoffMint() {
    }

    static void mintDelivered(CommunicationHandoffSpec site,
                              long attachEventId, Object carrier,
                              String field, String descriptor) {
        ActiveRegion active = attachConsumerRegion(site);
        if (active == null) {
            mintAmbient(site, carrier, field, descriptor);
            return;
        }
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

    private static ActiveRegion attachConsumerRegion(
            CommunicationHandoffSpec site) {
        return ConcolicRegionRuntime.declaringRegion(
                new ConcolicRegionRuntime.Declares.Port(
                        nonNull(site.portId())));
    }

    private static void mintHandoffVariable(
            ActiveRegion active, CommunicationHandoffSpec site,
            Object carrier, String field, String descriptor) {
        String portId = nonNull(site.portId());
        for (HandoffLeaf leaf : handoffLeaves(portId, carrier, field,
                descriptor)) {
            mintHandoffLeaf(active, portId, leaf);
        }
    }

    private static void mintHandoffLeaf(ActiveRegion active, String portId,
                                        HandoffLeaf leaf) {
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
            Endpoint consumer = RowRuntime.nextEndpoint(active.d3Address,
                    portId, WireExport.attemptOf(
                            RuntimeTraceContext.current()));
            String answer = consumer == null ? ""
                    : FocusedReplay.answer(consumer.id());
            if (!answer.isEmpty() && !RootMint.writeModeledField(leaf.owner,
                    leaf.signature(), descriptor, answer)) {
                RowRuntime.gap(GapKind.ASSIGNMENT_UNPLANTED,
                        GapClass.BLOCKING, portId,
                        "the wave's answer for this handoff could not be"
                                + " written into " + leaf.signature());
                return;
            }
            if (!answer.isEmpty()) {
                FocusedReplay.answered(!recordedValue.equals(ConcolicRegionRuntime
                        .recordedScalar(leaf.field.get(leaf.owner))));
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

    interface NativeAnswers {
        String answer(String endpointId);

        void planted(String endpointId, boolean written);
    }

    static Object answerNatively(String portId, Object value,
                                 OccurrenceAddress consumer,
                                 NativeAnswers answers) {
        ConcolicRegionRuntime.HandoffLeafCarrier carrier = carrierOf(value);
        String field = leafField(value);
        int attempt = WireExport.attemptOf(RuntimeTraceContext.current());
        String descriptor = "o".equals(field) ? "Ljava/lang/Object;"
                : field.toUpperCase();
        for (HandoffLeaf leaf : handoffLeaves(portId, carrier, field,
                descriptor)) {
            Endpoint endpoint = Identity.endpointAt(consumer, portId, attempt);
            String answer = endpoint == null ? null
                    : answers.answer(endpoint.id());
            if (answer == null) continue;
            answers.planted(endpoint.id(), RootMint.writeModeledField(
                    leaf.owner, leaf.signature(), javaTypeDescriptor(
                            leaf.field.getType().getTypeName()), answer));
        }
        return readBack(carrier, field);
    }

    private static ConcolicRegionRuntime.HandoffLeafCarrier carrierOf(
            Object value) {
        if (value instanceof Long) {
            return ConcolicRegionRuntime.HandoffLeafCarrier.of(
                    ((Long) value).longValue());
        }
        if (value instanceof Integer) {
            return ConcolicRegionRuntime.HandoffLeafCarrier.of(
                    ((Integer) value).intValue());
        }
        if (value instanceof Boolean) {
            return ConcolicRegionRuntime.HandoffLeafCarrier.of(
                    ((Boolean) value).booleanValue());
        }
        if (value instanceof Float) {
            return ConcolicRegionRuntime.HandoffLeafCarrier.of(
                    ((Float) value).floatValue());
        }
        if (value instanceof Double) {
            return ConcolicRegionRuntime.HandoffLeafCarrier.of(
                    ((Double) value).doubleValue());
        }
        return ConcolicRegionRuntime.HandoffLeafCarrier.of(value);
    }

    private static String leafField(Object value) {
        return value instanceof Long ? "j" : value instanceof Integer ? "i"
                : value instanceof Boolean ? "z" : value instanceof Float
                ? "f" : value instanceof Double ? "d" : "o";
    }

    private static Object readBack(
            ConcolicRegionRuntime.HandoffLeafCarrier carrier, String field) {
        switch (field) {
            case "j": return carrier.j;
            case "i": return carrier.i;
            case "z": return carrier.z;
            case "f": return carrier.f;
            case "d": return carrier.d;
            default: return carrier.o;
        }
    }

    private static void unminted(ActiveRegion active, String portId,
                                 String why) {
        RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                active.d3Address == null ? portId : active.d3Address.render(),
                "the boundary variable of the attach at " + portId + " was"
                        + " not minted, so the delivery names no occurrence"
                        + " two replays could be joined at: " + why);
    }

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

    static String handoffMintKey(String portId,
                                         String consumerAddress,
                                         int attachOrdinal,
                                         String elementPath) {
        if (nonNull(portId).isEmpty() || nonNull(consumerAddress).isEmpty()
                || nonNull(elementPath).isEmpty() || attachOrdinal < 1) {
            return "";
        }
        String identity = portId + "\n" + consumerAddress + "\n"
                + attachOrdinal + "\n" + elementPath;
        return HANDOFF_MINT_PREFIX + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8));
    }

    static String mintLabel(String mintKey, String portId) {
        return "HOFF." + ArtifactIO.sha256(mintKey + "\n"
                + nonNull(portId));
    }

    private static void publishAttachRow(Endpoint consumer, String portId,
                                         String symbol, String javaType,
                                         String arrival, String answer) {
        if (consumer == null || !RowRuntime.open()) return;
        try {
            Interactions.Delivery delivery = Interactions.delivery();
            RowRuntime.attachedAt(consumer, delivery.seq(), portId,
                    delivery.handle, delivery.correlationId, delivery.half,
                    symbol, javaType, arrival, !answer.isEmpty(), answer);
        } catch (Throwable unstated) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    portId,
                    "this delivery published no consumer endpoint row, so no"
                            + " arm can be keyed by it: "
                            + ConcolicRegionRuntime.rootCause(unstated));
        }
    }

    private static void mintAmbient(
            CommunicationHandoffSpec site, Object carrier, String field,
            String descriptor) {
        String portId = nonNull(site.portId());
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

    private static final Map<String, Integer> ATTACHES =
            new HashMap<String, Integer>();

    static int nextAttach(String consumer, String portId,
                          String elementPath) {
        String element = nonNull(consumer) + "\n" + nonNull(portId) + "\n"
                + nonNull(elementPath);
        synchronized (ATTACHES) {
            Integer previous = ATTACHES.get(element);
            int ordinal = previous == null ? 1 : previous + 1;
            ATTACHES.put(element, ordinal);
            return ordinal;
        }
    }

    static String ambientMintKey(String portId, String consumer,
                                 String elementPath) {
        return handoffMintKey(portId, consumer,
                nextAttach(consumer, portId, elementPath), elementPath);
    }

    private static final class HandoffLeaf {
        private final Object owner;
        private final Field field;
        private final String path;

        private HandoffLeaf(Object owner, Field field, String path) {
            this.owner = owner;
            this.field = field;
            this.path = path;
        }

        private String signature() {
            return exactFieldSignature(field);
        }
    }

    private static final int HANDOFF_LEAF_LIMIT = 64;

    private static List<HandoffLeaf> handoffLeaves(
            String portId, Object carrier, String field, String descriptor) {
        List<HandoffLeaf> leaves = primitiveLeaves(portId, carrier,
                declaredInstanceField(carrier, CARRIER_CLASS, field,
                        descriptor));
        if (leaves.isEmpty()) {
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

    private static int addPrimitiveLeaves(Object owner, String prefix,
                                          List<HandoffLeaf> leaves) {
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
