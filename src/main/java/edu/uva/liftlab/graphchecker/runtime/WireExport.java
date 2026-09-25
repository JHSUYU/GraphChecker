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
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
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
 * <p>The leaf is always a field of {@link
 * ConcolicRegionRuntime.HandoffLeafCarrier}, which stays there: woven
 * bytecode allocates it by binary name.  The runtime's own steps run with
 * observation paused, so they land in no path condition.</p>
 */
final class WireExport {
    private WireExport() {
    }

    /** One export: the staged handle (0 for a concrete leaf) and its event. */
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
        CommunicationHandoffSpec site;
        pauseObservation();
        try {
            site = site(portId, true);
        } finally {
            resumeObservation();
        }
        if (site == null || carrier == null) return;
        Export exported = export(carrier, field, descriptor);
        if (exported == null) return;
        if (!SymbolicMessageEnvelope.stage(site.portId(), exported.handle)) {
            // The row still states the endpoint; the loss is named.
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    site.portId(),
                    "the communication leaf could not enter the message");
        }
        publishExportRow(site, carrier, field, descriptor, exported.handle,
                exported.eventId);
    }

    /**
     * Exports one carrier leaf, or null when the VM refused it.  A concrete
     * leaf is still a leaf the message carried: handle 0.
     */
    private static Export export(Object carrier, String field,
                                 String descriptor) {
        pauseObservation();
        try {
            if (!leafNamed(field, descriptor)) return null;
            ConcolicVmBroker api = engine();
            long handle;
            // The VM reports the export's ledger event so the
            // row names the exact export.
            long[] exportEvent = new long[1];
            try {
                handle = api.exportExpression(carrier, CARRIER_CLASS, field,
                        descriptor, exportEvent);
            } catch (Throwable refused) {
                return null;
            }
            if (handle > 0L) return new Export(handle, exportEvent[0]);
            return handle == ConcolicVmBroker.NOT_SYMBOLIC
                    ? new Export(0L, 0L) : null;
        } finally {
            resumeObservation();
        }
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
        pauseObservation();
        try {
            if (!RowRuntime.open()) return;
            RuntimeTraceContext.View view = RuntimeTraceContext.current();
            ActiveRegion active = ConcolicRegionRuntime.activeRegion();
            // Producer address: the admitted activation's, else the
            // occurrence running here.
            OccurrenceAddress producer = active != null
                    && active.d3Address != null
                    ? active.d3Address
                    : RowRuntime.occurrenceHere(view.source == null ? ""
                            : view.source.key(), site.portId());
            if (active == null || active.d3Address == null) {
                RowRuntime.ambientActivation(producer);
            }
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
                        site.portId(),
                        "the exported leaf's expression could not be read: "
                                + ConcolicRegionRuntime.rootCause(unreadable));
            }
            RowRuntime.exported(producer, exportEventId, site.portId(),
                    handle, view.exchangeCorrelationId, attemptOf(view),
                    exported, descriptor, recordedValue);
        } catch (Throwable unstated) {
            // Publishing never ends a run, and never fails silently.
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    site.portId(),
                    "the export of this port published no endpoint row, so"
                            + " no delivery can be paired to it: "
                            + ConcolicRegionRuntime.rootCause(unstated));
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
            site = site(portId, false);
            handle = site == null ? 0L
                    : SymbolicMessageEnvelope.take(site.portId());
        } finally {
            resumeObservation();
        }
        if (site == null) {
            // Rule 5: an undeclared attach is named, not silent.
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
                long attachEventId = attach(carrier, field, descriptor,
                        handle);
                if (attachEventId > 0L) {
                    HandoffMint.mintDelivered(site, attachEventId, carrier,
                            field, descriptor);
                }
            } finally {
                resumeObservation();
            }
        } finally {
            Interactions.delivered();
        }
    }

    /**
     * The declared site of {@code portId}, whoever is running.
     *
     * <p>Propagation is a property of the value, not of the activation on
     * the stack, so the whole plan is asked, not just the active task.
     * Occurrences decide what gets published, never whether a value
     * propagates.</p>
     */
    private static CommunicationHandoffSpec site(String portId,
                                                 boolean exporting) {
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

    /**
     * Attaches {@code handle} onto one carrier leaf: the VM's attach event
     * id, or 0 when it refused.  An attach accepted with no attach event is
     * half an edge, so refused too.
     */
    private static long attach(Object carrier, String field,
                               String descriptor, long handle) {
        if (!leafNamed(field, descriptor)) return 0L;
        ConcolicVmBroker api = engine();
        // Both VALUE_HANDOFF endpoints leave the VM together.
        long[] attachEvent = new long[1];
        try {
            if (api.attachExpression(carrier, CARRIER_CLASS, field,
                    descriptor, handle, attachEvent) <= 0L) {
                return 0L;
            }
        } catch (Throwable refused) {
            return 0L;
        }
        return Math.max(0L, attachEvent[0]);
    }

    /** Whether a leaf names its field and type. */
    private static boolean leafNamed(String field, String descriptor) {
        return !firstNonBlank(field).isEmpty()
                && !firstNonBlank(descriptor).isEmpty();
    }
}
