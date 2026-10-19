package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;
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

import static edu.uva.liftlab.graphchecker.smt.JsonFields.trimmed;

final class WireExport {
    private WireExport() {
    }

    static final class Leaf {
        private final Object holder;
        private final String owner;
        private final String field;
        private final String descriptor;

        Leaf(Object holder, String owner, String field, String descriptor) {
            this.holder = holder;
            this.owner = owner;
            this.field = field;
            this.descriptor = descriptor;
        }
    }

    private static final class Export {
        private final long handle;
        private final long eventId;

        private Export(long handle, long eventId) {
            this.handle = handle;
            this.eventId = eventId;
        }
    }

    static void exportLeaf(String portId, Object carrier, String field,
                           String descriptor, Object builder) {
        if (carrier == null || trimmed(portId).isEmpty()) return;
        Leaf leaf = new Leaf(carrier, CARRIER_CLASS, field, descriptor);
        if (builder == null) {
            export(portId, leaf);
            return;
        }
        Export exported = export(leaf);
        if (exported.handle < 0L) {
            refused(portId, "export", exported.handle,
                    GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    "the message carries its field's value as a constant");
            return;
        }
        Endpoint producer = publishExportRow(portId, leaf, exported.handle,
                exported.eventId);
        pauseObservation();
        try {
            MessageCodec.set(builder, portId, exported.handle, producer);
        } finally {
            resumeObservation();
        }
    }

    static void export(String portId, Leaf leaf) {
        Export exported = export(leaf);
        if (exported.handle < 0L) {
            SymbolicMessageEnvelope.skip(portId);
            refused(portId, "export", exported.handle,
                    GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    "the message carries no element for it, so its"
                            + " consumer's attach pairs with no export");
            return;
        }
        Endpoint producer = publishExportRow(portId, leaf, exported.handle,
                exported.eventId);
        stage(portId, exported.handle, producer);
    }

    static void relay(String portId, MessageCodec.Element element) {
        stage(portId, element.handle, Interactions.pairing(portId,
                element.handle, element.correlationId, element.half)
                .producer());
    }

    static void stage(String portId, long handle, Endpoint producer) {
        if (!SymbolicMessageEnvelope.stage(portId, handle, producer)) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    portId,
                    "the communication leaf could not enter the message");
        }
    }

    private static Export export(Leaf leaf) {
        pauseObservation();
        try {
            if (!leafNamed(leaf.field, leaf.descriptor)) {
                return new Export(ConcolicVmBroker.MISSING_METADATA, 0L);
            }
            long handle;
            long[] exportEvent = new long[1];
            try {
                handle = engine().exportExpression(leaf.holder, leaf.owner,
                        leaf.field, leaf.descriptor, exportEvent);
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

    private static Endpoint publishExportRow(String portId, Leaf leaf,
                                             long handle,
                                             long exportEventId) {
        pauseObservation();
        try {
            if (!RowRuntime.open()) return null;
            RuntimeTraceContext.View view = RuntimeTraceContext.current();
            OccurrenceAddress producer = occurrenceHere(portId);
            JsonObject exported = null;
            String recordedValue = "";
            try {
                Field storage = declaredInstanceField(leaf.holder,
                        leaf.owner, leaf.field, leaf.descriptor);
                if (storage != null) {
                    Object value = storage.get(leaf.holder);
                    recordedValue = ConcolicRegionRuntime.recordedScalar(value);
                    JsonElement expression =
                            ConcolicRegionRuntime.engineExpression(
                                    engine().fieldExpression(leaf.holder,
                                            leaf.owner, leaf.field,
                                            leaf.descriptor, value));
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
                    leaf.descriptor, recordedValue);
        } catch (Throwable unstated) {
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

    static int attemptOf(RuntimeTraceContext.View view) {
        try {
            return Integer.parseInt(nonNull(view.exchangeAttemptId));
        } catch (NumberFormatException none) {
            return 0;
        }
    }

    static void attachLeaf(String portId, Object carrier, String field,
                           String descriptor, Object receiver) {
        CommunicationHandoffSpec site;
        MessageCodec.Element element;
        pauseObservation();
        try {
            site = attachSite(portId);
            element = site == null || carrier == null ? null
                    : site.codecField().isEmpty()
                    ? MessageCodec.Element.received(
                            SymbolicMessageEnvelope.take(site.portId()))
                    : MessageCodec.bound(receiver, site.portId());
        } finally {
            resumeObservation();
        }
        if (site == null) {
            RowRuntime.gap(GapKind.DECLARATION_MISSING, GapClass.DIAGNOSTIC,
                    trimmed(portId),
                    "a wire attach ran for a port no task of this campaign "
                            + "declares, so it filed nothing");
            return;
        }
        if (carrier == null || element == null) return;
        long handle = element.handle;
        Interactions.delivering(handle, element.correlationId, element.half);
        try {
            if (handle <= 0L) {
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
                    refused(site.portId(), "attach of handle " + handle,
                            attached, GapKind.ADMISSION_GAP,
                            GapClass.DIAGNOSTIC, "no admitted activation runs"
                                    + " here, so the value stays concrete and"
                                    + " nothing computed from it is a version"
                                    + " until the closure admits this one");
                } else {
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

    private static CommunicationHandoffSpec attachSite(String portId) {
        if (nonNull(portId).isEmpty()) return null;
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

    private static long attach(Object carrier, String field,
                               String descriptor, long handle) {
        if (!leafNamed(field, descriptor)) {
            return ConcolicVmBroker.MISSING_METADATA;
        }
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

    private static boolean leafNamed(String field, String descriptor) {
        return !firstNonBlank(field).isEmpty()
                && !firstNonBlank(descriptor).isEmpty();
    }
}
