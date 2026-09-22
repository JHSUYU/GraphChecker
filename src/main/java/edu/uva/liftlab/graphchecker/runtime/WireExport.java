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
 * <p>Out: the VM is asked to export the live expression of the carrier leaf
 * the instrumented frame stored into, the handle is staged on the outbound
 * message, and the row states the producer endpoint whether or not a region
 * was live -- the site ran and the message carries the value, so which
 * occurrence produced it is what the row says about itself, not a condition
 * on saying it.  In: the staged element is taken, the producer's expression
 * is attached onto the arrived carrier leaf, and the consumer's boundary
 * variable is minted by {@link HandoffMint}.</p>
 *
 * <p>The carrier class itself stays on {@link ConcolicRegionRuntime}:
 * {@code CausynthPipeline} allocates it by the binary name
 * {@code ...ConcolicRegionRuntime$HandoffLeafCarrier}, so moving it would
 * change woven bytecode.</p>
 *
 * <p>Propagation is a property of the value, not of the activation on the
 * stack -- {@link #site} therefore asks the whole plan, not just the live
 * task.  Occurrences decide what gets published, never whether a value
 * propagates.</p>
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

        /**
         * The VM ledger event of this exact attach.
         *
         * <p>README {@code RPC-1}: the second endpoint of the {@code
         * VALUE_HANDOFF} edge.</p>
         */
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
        // README RPC-1: the VM reports the export's own ledger event here,
        // so the producer's interaction row can name the exact export it
        // published instead of leaving the Composer to count port
        // observations for it.
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
                HandoffMint.mintDelivered(declared, result, owner, declaringClass,
                        fieldName, descriptor, carried.producerTaskId(),
                        carried.producerOccurrenceId());
            }
            return result;
        } finally {
            ConcolicRegionRuntime.endBookkeeping();
        }
    }

    /** Stages one VM handle and its producer on the next outbound message. */
    private static boolean stageMessageExpression(String portId,
                                                  long handle) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        // The producer site ran, so the message carries the value.  Which
        // occurrence produced it and which the plan addressed are what the
        // entry says about itself, not conditions on saying it.
        String producerTask = active == null ? UNPLANNED_ENDPOINT
                : active.activation.taskId;
        String producerOccurrence = active == null ? UNPLANNED_ENDPOINT
                : active.occurrenceId();
        return SymbolicMessageEnvelope.stage(portId, handle, producerTask,
                producerOccurrence);
    }

    /**
     * Stands in for an endpoint no plan named.
     *
     * <p>A leaf may be staged or taken under an identity the plan did not
     * select.  The value is still the value; the entry says plainly that its
     * endpoint was not planned rather than pretending to an occurrence.</p>
     */
    static final String UNPLANNED_ENDPOINT = "UNPLANNED";

    /**
     * Opens the frame around one message instance being serialized.
     *
     * <p>A declared port is one pair of bytecode sites, and a protocol sends
     * many unrelated values of that shape through it.  The frame is the thing
     * whose single construction builds one instance of the value the port
     * belongs to; leaves staged inside it are addressed within it, so two
     * groups of the same shape in one message stay apart.</p>
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
     * Opens the frame around one message instance being decoded.
     *
     * <p>The mirror of {@link #pushOutboundFrame}: the receiver counts
     * its frames the way the sender counted theirs, so the k-th frame means
     * the same thing on both sides without either naming the other.</p>
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
     * Exports the live expression of one declared communication port.
     *
     * <p>The value arrives on a {@link ConcolicRegionRuntime.HandoffLeafCarrier} the
     * <em>instrumented frame</em> allocated and stored into, because a broker
     * leaf is an exact instance field while a cut argument is a local - and
     * because only the application's own frame propagates a value's expression
     * into a field.</p>
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
            // The value crossed and the message could not carry its
            // expression: the row still states the endpoint, and the loss
            // is named rather than left as an export nobody can pair.
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
     * States one export as an endpoint the delivery can be paired to.
     *
     * <p>Every export, whether or not a region was live: the producer site
     * ran and the message carries the value, so the row exists and says
     * which occurrence produced it -- a degraded one when no live region
     * did, which is still an endpoint an arm can be keyed by (R-I1) and is
     * what the OUT side used to spell {@code UNPLANNED}.</p>
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
            // One door for a producer address: the admitted activation's own
            // (which Identity.currentOccurrence minted it as), else the
            // occurrence running here by the same door.
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
                // The export happened; what it carried could not be read
                // back here, and the row says the endpoint without it.
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
            // Publishing never ends a workload run -- and it never passes
            // in silence either: the value crossed the port and no row
            // states the endpoint, so nothing downstream can pair the
            // delivery to it.
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
     * Attaches the exported expression of one declared communication port.
     *
     * <p>After a successful attach the carrier leaf <em>denotes the sender's
     * expression</em>; the instrumented frame reads it straight back into its
     * own local, so the receiver's later arithmetic, branches and exports
     * build on that term directly.</p>
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
            // A capture ran for a port no task of this campaign declares.
            // Rule 5: the run says so rather than returning in silence --
            // an attach that files nothing and an attach nobody planned
            // read identically from the corpus, and only one of them is a
            // coverage question.
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
     * Files one delivery on the occurrence it arrived in.
     *
     * <p>Split out so the delivery's own pairing evidence -- the VM handle
     * the producer staged -- is in force for the whole attach, including
     * the mint, without threading it through four signatures.</p>
     */
    private static void attachDeliveredLeaf(
            CommunicationHandoffSpec site, Object carrier, String field,
            String descriptor, SymbolicMessageEnvelope.Entry carried,
            long handle, boolean leafCarried) {
        if (!leafCarried || handle <= 0L) {
            // The delivery carried no producer expression, and the mint
            // happens anyway.  v_H is the consumer's boundary variable,
            // minted at the consumer's declared capture on the value that
            // ARRIVED; the envelope element only supplies e_p, which is one
            // member of H's family and not a condition of H existing.
            // Absent, the row says so and this delivery contributes no
            // family arm -- which is exactly right for a flip replay whose
            // job is the consumer's path under an assigned v_H, with the
            // producing node running concretely.
            //
            // Two ways for it to be absent, one fact for the consumer.  The
            // message may carry no element for this decode at all; or it may
            // carry one the producer staged with handle 0, which is what
            // exportCommunicationLeaf stages for a leaf the VM answered
            // NOT_SYMBOLIC -- "a concrete leaf is still a leaf the message
            // carried".  Either way there is no e_p and there is an arrived
            // value, so both take this path and the row states
            // elementAbsent.
            //
            // Refusing here left the assignment unapplied: on hdfs-17899
            // bug3 the flip replay of the target published zero handoff
            // rows, the fatal read still found the recorded key, and the
            // obligation ended REPLAY_NOT_ADMITTED with no primary case.
            HandoffMint.mintArrived(site, carrier, field, descriptor);
            return;
        }
        attachDeclaredCommunicationExpression(carrier, ConcolicRegionRuntime.CARRIER_CLASS, field,
                descriptor, carried, site);
    }

    /** The declared site of {@code portId} in this occurrence's plan. */
    /**
     * The declared site of {@code portId}, whoever is running.
     *
     * <p>Propagation is a property of the value, not of the activation that
     * happens to be on the stack.  The same conversion runs under several
     * region identities -- the one the plan selected for the port and the
     * ones that merely call the same helper -- and the leaf crossing the
     * wire is the same leaf in all of them.  Asking only the active task
     * meant a value arriving under an unselected identity was dropped, which
     * is how the four conversions that fill a DataNode's key map received no
     * producer expression at all.  Occurrences decide what gets published,
     * never whether a value propagates.</p>
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
        // README RPC-1: both endpoints of the VALUE_HANDOFF edge leave the VM
        // together.
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
            // A VM that accepted the attach but named no attach event has told
            // us half an edge.
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

    /**
     * One refused broker call, as the call's own answer.
     *
     * <p>No {@code detail}: the string every caller used to build here was
     * never read by anything, and the diagnostic {@code record(...)} that
     * was to have read it had decayed to an identity function.  What the
     * callers act on is {@link HandoffResult#ok()} and the status.</p>
     */
    private static HandoffResult failed(String stage, int status,
                                        long handle) {
        return new HandoffResult(stage, status, handle, null);
    }
}
