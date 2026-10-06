package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.CARRIER_CLASS;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.pauseObservation;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.resumeObservation;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.configuration;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.declaredInstanceField;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;

import java.lang.reflect.Field;

/**
 * The wire's near half (SYMBOL-SCOPE §6.3): a value crossing one declared
 * communication port, and the endpoint row that says it crossed.
 *
 * <p>Out: export the carrier leaf's expression, stage the handle on the
 * outbound message, and state the producer endpoint whether or not a region
 * was live.  In: take the staged element, attach the producer's expression
 * onto the arrived leaf, and mint the consumer's boundary variable via
 * {@link HandoffMint}.</p>
 *
 * <p>The leaf is always a field of {@link
 * ConcolicRegionRuntime.HandoffLeafCarrier}, which stays there: woven
 * bytecode allocates it by binary name.  The runtime's own steps run with
 * observation paused, so they land in no path condition.</p>
 */
final class WireExport {
    private WireExport() {
    }

    /**
     * One export: the staged handle (0 for a concrete leaf, negative for the
     * status the VM refused with) and its event.
     */
    private static final class Export {
        private final long handle;
        /** The VM ledger event of the export, or 0. */
        private final long eventId;

        private Export(long handle, long eventId) {
            this.handle = handle;
            this.eventId = eventId;
        }
    }

    /** Runs one step of the runtime's own, unobserved by the VM. */
    private static void paused(Runnable step) {
        pauseObservation();
        try {
            step.run();
        } finally {
            resumeObservation();
        }
    }

    /**
     * Opens the frame around one message instance being serialized; leaves
     * staged inside are addressed within it, so two same-shaped groups in one
     * message stay apart.
     */
    static void pushOutboundFrame() {
        paused(SymbolicMessageEnvelope::pushOutboundFrame);
    }

    /** Closes the frame {@link #pushOutboundFrame} opened. */
    static void popOutboundFrame() {
        paused(SymbolicMessageEnvelope::popOutboundFrame);
    }

    /**
     * Mirror of {@link #pushOutboundFrame}: the k-th frame means the same
     * thing on both sides.
     */
    static void pushInboundFrame() {
        paused(SymbolicMessageEnvelope::pushInboundFrame);
    }

    /** Closes the frame {@link #pushInboundFrame} opened. */
    static void popInboundFrame() {
        paused(SymbolicMessageEnvelope::popInboundFrame);
    }

    /**
     * Exports the live expression of one declared communication port, read
     * from the carrier leaf the instrumented frame stored into (a broker
     * leaf must be a field).
     */
    static void exportLeaf(String portId, Object carrier, String field,
                           String descriptor) {
        // The woven call is the declaration: every export of the program is
        // woven (RuntimeRegionPlanner#exportSites), planned or not.
        if (carrier == null || Text.safe(portId).isEmpty()) return;
        Export exported = export(carrier, field, descriptor);
        if (exported.handle < 0L) {
            refused(portId, "export", exported.handle,
                    GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    "the message carries no element for it, so its"
                            + " consumer's attach pairs with no export");
            return;
        }
        // The endpoint first: the message the leaf enters files it as its
        // own producer at its door (SymbolicMessageEnvelope#carriedBy).
        Endpoint producer = publishExportRow(portId, carrier, field,
                descriptor, exported.handle, exported.eventId);
        if (!SymbolicMessageEnvelope.stage(portId, exported.handle,
                producer)) {
            // The row still states the endpoint; the loss is named.
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    portId,
                    "the communication leaf could not enter the message");
        }
    }

    /**
     * Exports one carrier leaf.  A concrete leaf is still a leaf the message
     * carried: handle 0.
     */
    private static Export export(Object carrier, String field,
                                 String descriptor) {
        pauseObservation();
        try {
            if (!leafNamed(field, descriptor)) {
                return new Export(ConcolicVmBroker.MISSING_METADATA, 0L);
            }
            long handle;
            // The VM reports the export's ledger event so the
            // row names the exact export.
            long[] exportEvent = new long[1];
            try {
                handle = engine().exportExpression(carrier, CARRIER_CLASS,
                        field, descriptor, exportEvent);
            } catch (Throwable refused) {
                handle = ConcolicVmBroker.INVOCATION_FAILED;
            }
            if (handle > 0L) return new Export(handle, exportEvent[0]);
            if (handle == ConcolicVmBroker.NOT_SYMBOLIC) {
                return new Export(0L, 0L);
            }
            return new Export(handle < 0L ? handle
                    : ConcolicVmBroker.MALFORMED_RESULT, 0L);
        } finally {
            resumeObservation();
        }
    }

    /**
     * States one export as an endpoint a delivery can be paired to -- every
     * export, with a degraded producer occurrence when no region is live
     * (still keyable, IDENTITY §4): the endpoint, or null when no session
     * is open or the row could not be stated.
     */
    private static Endpoint publishExportRow(String portId,
                                         Object carrier, String field,
                                         String descriptor, long handle,
                                         long exportEventId) {
        pauseObservation();
        try {
            if (!RowRuntime.open()) return null;
            RuntimeTraceContext.View view = RuntimeTraceContext.current();
            OccurrenceAddress producer = occurrenceHere(portId);
            JsonObject exported = null;
            String recordedValue = "";
            try {
                Field storage = declaredInstanceField(carrier, CARRIER_CLASS,
                        field, descriptor);
                if (storage != null) {
                    Object value = storage.get(carrier);
                    recordedValue = ConcolicRegionRuntime.recordedScalar(value);
                    JsonElement expression =
                            ConcolicRegionRuntime.engineExpression(
                                    engine().fieldExpression(carrier,
                                            CARRIER_CLASS, field, descriptor,
                                            value));
                    if (expression != null && expression.isJsonObject()) {
                        exported = expression.getAsJsonObject();
                    }
                }
            } catch (Throwable unreadable) {
                RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        portId,
                        "the exported leaf's expression could not be read: "
                                + ConcolicRegionRuntime.rootCause(unreadable));
            }
            return RowRuntime.exported(producer, exportEventId,
                    portId, handle, attemptOf(view), exported,
                    descriptor, recordedValue);
        } catch (Throwable unstated) {
            // Publishing never ends a run, and never fails silently.
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    portId,
                    "the export of this port published no endpoint row, so"
                            + " no delivery can be paired to it: "
                            + ConcolicRegionRuntime.rootCause(unstated));
            return null;
        } finally {
            resumeObservation();
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
     * instrumented frame reads back into its local.  The delivery is filed
     * on the occurrence it arrived in, with the producer's handle in force
     * ({@link Interactions#delivering}) for the whole attach.
     */
    static void attachLeaf(String portId, Object carrier, String field,
                           String descriptor) {
        CommunicationHandoffSpec site;
        long handle;
        pauseObservation();
        try {
            site = attachSite(portId);
            // With no carrier nothing is taken: the element stays for the
            // message's end to name as unattached.
            handle = site == null || carrier == null ? 0L
                    : SymbolicMessageEnvelope.take(site.portId());
        } finally {
            resumeObservation();
        }
        if (site == null) {
            // An undeclared attach is named, not silent.
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    Text.safe(portId),
                    "a wire attach ran for a port no task of this campaign "
                            + "declares, so it filed nothing");
            return;
        }
        if (carrier == null) return;
        Interactions.delivering(handle);
        try {
            if (handle <= 0L) {
                // No producer expression: still mint v_H on the arrived
                // value.  e_p is one family arm, not a condition of v_H
                // existing; refusing here leaves a flip replay's assignment
                // unapplied.
                HandoffMint.mintArrived(site, carrier, field, descriptor);
                return;
            }
            pauseObservation();
            try {
                long attached = attach(carrier, field, descriptor, handle);
                if (attached > 0L) {
                    HandoffMint.mintDelivered(site, attached, carrier, field,
                            descriptor);
                } else if (ConcolicRegionRuntime.activeRegion() == null) {
                    // SOLR-18413 s45: a callback no activation ran parsed the
                    // value, and its parse won the cache the leader read.
                    refused(site.portId(), "attach of handle " + handle,
                            attached, GapKind.ADMISSION_GAP,
                            GapClass.DIAGNOSTIC, "no admitted activation runs"
                                    + " here, so the value stays concrete and"
                                    + " nothing computed from it is a version"
                                    + " until the closure admits this one");
                } else {
                    // The refusal is this occurrence's: what rests on it
                    // composes with the constant (Composer#frames).
                    refused(site.portId(), "attach of handle " + handle,
                            attached, GapKind.UNSTATED_VALUE,
                            GapClass.DIAGNOSTIC, "the admitted activation here"
                                    + " computes on the arrived value as a"
                                    + " constant, and no attach row says a"
                                    + " producer sent it, so a path or arm"
                                    + " whose closure reaches this occurrence"
                                    + " rests on that constant");
                }
            } finally {
                resumeObservation();
            }
        } finally {
            Interactions.delivered();
        }
    }

    /**
     * The declared attach site of {@code portId}, whoever is running.
     *
     * <p>Propagation is a property of the value, not of the activation on
     * the stack, so the whole plan is asked, not just the active task.
     * Occurrences decide what gets published, never whether a value
     * propagates.</p>
     */
    private static CommunicationHandoffSpec attachSite(String portId) {
        if (safe(portId).isEmpty()) return null;
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active != null) {
            CommunicationHandoffSpec declared =
                    active.activation.attachSite(portId);
            if (declared != null) return declared;
        }
        for (ConcolicTaskPlan.RuntimeTask task : configuration().tasks) {
            CommunicationHandoffSpec declared = task.attachSite(portId);
            if (declared != null) return declared;
        }
        return null;
    }

    /**
     * Attaches {@code handle} onto one carrier leaf: the VM's attach event
     * id, or the status it refused with (never positive).  An attach
     * accepted with no attach event is half an edge, so refused too.
     */
    private static long attach(Object carrier, String field,
                               String descriptor, long handle) {
        if (!leafNamed(field, descriptor)) {
            return ConcolicVmBroker.MISSING_METADATA;
        }
        // Both VALUE_HANDOFF endpoints leave the VM together.
        long[] attachEvent = new long[1];
        long exportEvent;
        try {
            exportEvent = engine().attachExpression(carrier, CARRIER_CLASS,
                    field, descriptor, handle, attachEvent);
        } catch (Throwable refused) {
            return ConcolicVmBroker.INVOCATION_FAILED;
        }
        if (exportEvent < 0L) return exportEvent;
        return exportEvent > 0L && attachEvent[0] > 0L ? attachEvent[0]
                : ConcolicVmBroker.MALFORMED_RESULT;
    }

    /**
     * Names one leaf the VM would not carry across {@code portId}: the
     * occurrence it happened in, the step and the VM's status.  A refusal is
     * a row, never a missing one; the caller says what it costs.
     */
    private static void refused(String portId, String step, long status,
                                GapKind kind, GapClass cls,
                                String consequence) {
        pauseObservation();
        try {
            OccurrenceAddress here = occurrenceHere(portId);
            RowRuntime.gap(kind, cls, here == null ? portId : here.render(),
                    "the VM refused the " + step + " at " + portId + " ("
                            + ConcolicVmBroker.statusName(status) + "): "
                            + consequence);
        } finally {
            resumeObservation();
        }
    }

    /**
     * The occurrence a port event runs in: the admitted activation's, else
     * the one running here, stated as an unselected activation (still
     * keyable, IDENTITY §4).
     */
    private static OccurrenceAddress occurrenceHere(String portId) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active != null && active.d3Address != null) {
            return active.d3Address;
        }
        RuntimeTraceContext.View view = RuntimeTraceContext.current();
        OccurrenceAddress here = RowRuntime.occurrenceHere(
                view.source == null ? "" : view.source.key(), portId);
        RowRuntime.ambientActivation(here);
        return here;
    }

    /** Whether a leaf names its field and type. */
    private static boolean leafNamed(String field, String descriptor) {
        return !firstNonBlank(field).isEmpty()
                && !firstNonBlank(descriptor).isEmpty();
    }
}
