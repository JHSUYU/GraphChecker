package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.configuration;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.declaredInstanceField;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;

import java.lang.reflect.Field;

/**
 * R4's near half: a value crossing one declared communication port, and the
 * endpoint row that says it crossed.
 *
 * <p>Out: export the carrier leaf's expression, stage the handle on the
 * outbound message, and state the producer endpoint whether or not a region
 * was live.  In: take the staged element, attach the producer's expression
 * onto the arrived leaf, and mint the consumer's boundary variable via
 * {@link HandoffMint}.</p>
 *
 * <p>The carrier class stays on {@link ConcolicRegionRuntime}: woven bytecode
 * allocates it by binary name.</p>
 */
final class WireExport {
    private WireExport() {
    }

    /** Result of one VM symbolic-expression export or attach. */
    static final class HandoffResult {
        private final String stage;
        private final int status;
        private final long handle;
        /** The VM ledger events of a successful call, or {@code null}. */
        final JsonObject record;

        private HandoffResult(String stage, int status, long handle,
                              JsonObject record) {
            this.stage = stage;
            this.status = status;
            this.handle = handle;
            this.record = record;
        }

        public boolean ok() {
            return status == ConcolicVmBroker.OK;
        }

        /** Named reason for a failure; empty for a successful call. */
        public String reason() {
            return ConcolicVmBroker.describe(status);
        }

        private long handle() {
            return handle;
        }

        @Override
        public String toString() {
            return "HandoffResult[" + stage + " status=" + status
                    + (ok() ? "" : " " + reason())
                    + " handle=" + handle + "]";
        }
    }

    private static HandoffResult exportSymbolicLeaf(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        HandoffResult result;
        ConcolicRegionRuntime.beginBookkeeping();
        try {
            result = exportOneLeaf(owner, declaringClass, fieldName,
                    descriptor);
        } finally {
            ConcolicRegionRuntime.endBookkeeping();
        }
        return result;
    }

    private static HandoffResult exportOneLeaf(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        String missing = missingFieldMetadata(owner, declaringClass,
                fieldName, descriptor);
        if (!missing.isEmpty()) {
            return failed("EXPORT", ConcolicVmBroker.MISSING_METADATA, 0L);
        }
        ConcolicVmBroker api = engine();
        long handle;
        // README RPC-1: the VM reports the export's ledger event so the row
        // names the exact export.
        long[] exportEvent = new long[1];
        try {
            handle = api.exportExpression(owner, declaringClass, fieldName,
                    descriptor, exportEvent);
        } catch (Throwable throwable) {
            return failed("EXPORT", ConcolicVmBroker.INVOCATION_FAILED, 0L);
        }
        if (handle <= 0L) {
            return failed("EXPORT", exportStatus(handle), 0L);
        }
        JsonObject exported = new JsonObject();
        exported.addProperty("exportEventId", exportEvent[0]);
        return new HandoffResult("EXPORT", ConcolicVmBroker.OK, handle,
                exported);
    }

    /**
     * Attaches one receive whose destination this occurrence's plan declares
     * as a communication port.
     */
    private static HandoffResult attachDeclaredCommunicationExpression(
            Object owner, String declaringClass, String fieldName,
            String descriptor, SymbolicMessageEnvelope.Entry carried,
            CommunicationHandoffSpec declared) {
        ConcolicRegionRuntime.beginBookkeeping();
        try {
            HandoffResult result = attach(owner, declaringClass,
                    fieldName, descriptor, carried.handle());
            if (result.ok()) {
                HandoffMint.mintDelivered(declared, result, owner,
                        declaringClass, fieldName, descriptor);
            }
            return result;
        } finally {
            ConcolicRegionRuntime.endBookkeeping();
        }
    }

    /** Stages one VM handle on the next outbound message. */
    private static boolean stageMessageExpression(String portId,
                                                  long handle) {
        return SymbolicMessageEnvelope.stage(portId, handle);
    }

    /**
     * Opens the frame around one message instance being serialized; leaves
     * staged inside are addressed within it, so two same-shaped groups in one
     * message stay apart.
     */
    static void pushOutboundFrame() {
        ConcolicRegionRuntime.beginBookkeeping();
        try {
            SymbolicMessageEnvelope.pushOutboundFrame();
        } finally {
            ConcolicRegionRuntime.endBookkeeping();
        }
    }

    /** Closes the frame {@link #pushOutboundFrame} opened. */
    static void popOutboundFrame() {
        ConcolicRegionRuntime.beginBookkeeping();
        try {
            SymbolicMessageEnvelope.popOutboundFrame();
        } finally {
            ConcolicRegionRuntime.endBookkeeping();
        }
    }

    /**
     * Mirror of {@link #pushOutboundFrame}: the k-th frame means the same
     * thing on both sides.
     */
    static void pushInboundFrame() {
        ConcolicRegionRuntime.beginBookkeeping();
        try {
            SymbolicMessageEnvelope.pushInboundFrame();
        } finally {
            ConcolicRegionRuntime.endBookkeeping();
        }
    }

    /** Closes the frame {@link #pushInboundMessageFrame} opened. */
    static void popInboundFrame() {
        ConcolicRegionRuntime.beginBookkeeping();
        try {
            SymbolicMessageEnvelope.popInboundFrame();
        } finally {
            ConcolicRegionRuntime.endBookkeeping();
        }
    }

    /**
     * Exports the live expression of one declared communication port, read
     * from the {@link ConcolicRegionRuntime.HandoffLeafCarrier} the
     * instrumented frame stored into (a broker leaf must be a field).
     */
    static void exportLeaf(String portId, Object carrier, String field,
                           String descriptor) {
        CommunicationHandoffSpec site;
        ConcolicRegionRuntime.beginBookkeeping();
        try {
            site = site(portId, true);
        } finally {
            ConcolicRegionRuntime.endBookkeeping();
        }
        if (site == null || carrier == null) return;
        HandoffResult result = exportSymbolicLeaf(carrier, ConcolicRegionRuntime.CARRIER_CLASS,
                field, descriptor);
        // A concrete leaf is still a leaf the message carried.
        if (!result.ok()
                && result.status != ConcolicVmBroker.NOT_SYMBOLIC) {
            return;
        }
        long handle = result.ok() ? result.handle() : 0L;
        if (!stageMessageExpression(site.portId(), handle)) {
            // The row still states the endpoint; the loss is named.
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                            .UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass
                            .DIAGNOSTIC, site.portId(),
                    "the communication leaf could not enter the message");
        }
        publishExportRow(site, carrier, field, descriptor, handle,
                result.ok() ? optionalLongInteger(result.record,
                        "exportEventId", 0L) : 0L);
    }

    /**
     * States one export as an endpoint a delivery can be paired to -- every
     * export, with a degraded producer occurrence when no region is live
     * (still keyable, R-I1).
     */
    private static void publishExportRow(CommunicationHandoffSpec site,
                                         Object carrier, String field,
                                         String descriptor, long handle,
                                         long exportEventId) {
        ConcolicRegionRuntime.beginBookkeeping();
        try {
            if (!RowRuntime.open()) return;
            RuntimeTraceContext.View view = RuntimeTraceContext.current();
            ActiveRegion active = ConcolicRegionRuntime.activeRegion();
            // Producer address: the admitted activation's, else the
            // occurrence running here.
            edu.uva.liftlab.graphchecker.contract.OccurrenceAddress
                    producer = active != null && active.d3Address != null
                    ? active.d3Address
                    : RowRuntime.occurrenceHere(view.source == null ? ""
                            : view.source.key(), site.portId());
            if (active == null || active.d3Address == null) {
                RowRuntime.ambientActivation(producer);
            }
            JsonObject exported = null;
            String recordedValue = "";
            try {
                Field storage = declaredInstanceField(carrier, ConcolicRegionRuntime.CARRIER_CLASS,
                        field, descriptor);
                if (storage != null) {
                    Object value = storage.get(carrier);
                    recordedValue = ConcolicRegionRuntime.recordedScalar(value);
                    JsonElement expression = ConcolicRegionRuntime.engineExpression(
                            engine().fieldExpression(carrier, ConcolicRegionRuntime.CARRIER_CLASS,
                                    field, descriptor, value));
                    if (expression != null && expression.isJsonObject()) {
                        exported = expression.getAsJsonObject();
                    }
                }
            } catch (Throwable unreadable) {
                RowRuntime.gap(
                        edu.uva.liftlab.graphchecker.contract.GapKind
                                .UNSTATED_VALUE,
                        edu.uva.liftlab.graphchecker.contract.GapClass
                                .DIAGNOSTIC, site.portId(),
                        "the exported leaf's expression could not be read: "
                                + ConcolicRegionRuntime.rootCause(unreadable));
            }
            RowRuntime.exported(producer, exportEventId, site.portId(),
                    handle, view.exchangeCorrelationId, attemptOf(view),
                    exported, descriptor, recordedValue);
        } catch (Throwable unstated) {
            // Publishing never ends a run, and never fails silently.
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC, site.portId(),
                    "the export of this port published no endpoint row, so"
                            + " no delivery can be paired to it: "
                            + ConcolicRegionRuntime.rootCause(unstated));
        } finally {
            ConcolicRegionRuntime.endBookkeeping();
        }
    }

    /** The transport's retry number for this leg, or 0. */
    static int attemptOf(RuntimeTraceContext.View view) {
        try {
            return Integer.parseInt(safe(view.exchangeAttemptId));
        } catch (NumberFormatException none) {
            return 0;
        }
    }

    /**
     * Attaches the exported expression of one declared communication port;
     * the carrier leaf then denotes the sender's expression, which the
     * instrumented frame reads back into its local.
     */
    static void attachLeaf(String portId, Object carrier, String field,
                           String descriptor) {
        CommunicationHandoffSpec site;
        SymbolicMessageEnvelope.Entry carried;
        long handle;
        boolean leafCarried;
        ConcolicRegionRuntime.beginBookkeeping();
        try {
            site = site(portId, false);
            carried = site == null ? null
                    : SymbolicMessageEnvelope.take(site.portId());
            leafCarried = carried != null && carried.present();
            handle = carried == null ? 0L : carried.handle();
        } finally {
            ConcolicRegionRuntime.endBookkeeping();
        }
        if (site == null) {
            // Rule 5: an undeclared attach is named, not silent.
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                            .DECLARATION_MISSING,
                    edu.uva.liftlab.graphchecker.contract.GapClass
                            .DIAGNOSTIC, Text.safe(portId),
                    "a wire attach ran for a port no task of this campaign "
                            + "declares, so it filed nothing");
            return;
        }
        if (carrier == null) {
            return;
        }
        Interactions.delivering(handle);
        try {
            attachDeliveredLeaf(site, carrier, field, descriptor, carried,
                    handle, leafCarried);
        } finally {
            Interactions.delivered();
        }
    }

    /**
     * Files one delivery on the occurrence it arrived in, with the producer's
     * handle in force (via {@link Interactions#delivering}) for the whole
     * attach.
     */
    private static void attachDeliveredLeaf(
            CommunicationHandoffSpec site, Object carrier, String field,
            String descriptor, SymbolicMessageEnvelope.Entry carried,
            long handle, boolean leafCarried) {
        if (!leafCarried || handle <= 0L) {
            // No producer expression (no element, or a NOT_SYMBOLIC one
            // staged with handle 0): still mint v_H on the arrived value.
            // e_p is one family arm, not a condition of v_H existing;
            // refusing here leaves a flip replay's assignment unapplied.
            HandoffMint.mintArrived(site, carrier, field, descriptor);
            return;
        }
        attachDeclaredCommunicationExpression(carrier, ConcolicRegionRuntime.CARRIER_CLASS, field,
                descriptor, carried, site);
    }

    /**
     * The declared site of {@code portId}, whoever is running.
     *
     * <p>Propagation is a property of the value, not of the activation on
     * the stack, so the whole plan is asked, not just the active task.
     * Occurrences decide what gets published, never whether a value
     * propagates.</p>
     */
    static CommunicationHandoffSpec site(
            String portId, boolean exporting) {
        if (safe(portId).isEmpty()) return null;
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active != null) {
            CommunicationHandoffSpec declared =
                    active.activation.communicationHandoff(portId, exporting);
            if (declared != null) return declared;
        }
        for (ConcolicTaskPlan.RuntimeTask task : configuration().tasks) {
            CommunicationHandoffSpec declared =
                    task.communicationHandoff(portId, exporting);
            if (declared != null) return declared;
        }
        return null;
    }

    private static HandoffResult attach(
            Object owner, String declaringClass, String fieldName,
            String descriptor, long handle) {
        String missing = missingFieldMetadata(owner, declaringClass,
                fieldName, descriptor);
        if (handle <= 0L) {
            missing = firstNonBlank(missing,
                    "attach needs a positive handle");
        }
        if (!missing.isEmpty()) {
            return failed("ATTACH", ConcolicVmBroker.MISSING_METADATA,
                    handle);
        }
        ConcolicVmBroker api = engine();
        long exportEventId;
        // README RPC-1: both VALUE_HANDOFF endpoints leave the VM together.
        long[] attachEvent = new long[1];
        try {
            exportEventId = api.attachExpression(owner, declaringClass,
                    fieldName, descriptor, handle, attachEvent);
        } catch (Throwable throwable) {
            return failed("ATTACH", ConcolicVmBroker.INVOCATION_FAILED,
                    handle);
        }
        if (exportEventId <= 0L) {
            return failed("ATTACH", exportStatus(exportEventId), handle);
        }
        if (attachEvent[0] <= 0L) {
            // Accepted with no attach event: half an edge.
            return failed("ATTACH", ConcolicVmBroker.MALFORMED_RESULT,
                    handle);
        }
        JsonObject success = new JsonObject();
        success.addProperty("exportEventId", exportEventId);
        success.addProperty("attachEventId", attachEvent[0]);
        return new HandoffResult("ATTACH",
                ConcolicVmBroker.OK, handle, success);
    }

    private static String missingFieldMetadata(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        if (owner == null) return "handoff leaf has no owner instance";
        if (firstNonBlank(declaringClass).isEmpty()
                || firstNonBlank(fieldName).isEmpty()
                || firstNonBlank(descriptor).isEmpty()) {
            return "handoff leaf has no exact declaring class, field name "
                    + "and type descriptor";
        }
        return "";
    }

    /** Maps a non-positive {@code exportExpression} answer onto a status. */
    private static int exportStatus(long handle) {
        if (handle == 0L || handle < Integer.MIN_VALUE) {
            return ConcolicVmBroker.MALFORMED_RESULT;
        }
        return (int) handle;
    }

    /** One refused broker call; callers act on the status only. */
    private static HandoffResult failed(String stage, int status,
                                        long handle) {
        return new HandoffResult(stage, status, handle, null);
    }
}
