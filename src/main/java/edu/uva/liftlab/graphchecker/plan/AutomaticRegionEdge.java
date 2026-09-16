package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.runtime.OccurrenceBinding;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;

/** Evidence gate shared by graph discovery and SMT preparation. */
public final class AutomaticRegionEdge {
    public static final String RUNTIME_PROTOCOL_EDGE_KIND =
            "RUNTIME_PROTOCOL_FLOW";
    /**
     * A fault decision observed immediately before the request half of the
     * same transaction whose response carries a demanded value.
     */
    public static final String RUNTIME_REQUEST_CONTROL_EDGE_KIND =
            "RUNTIME_REQUEST_CONTROL";
    /** Runtime authority for {@link #RUNTIME_REQUEST_CONTROL_EDGE_KIND}. */
    public static final String EXACT_REQUEST_FAULT_CONTROL_AUTHORITY =
            "EXACT_RUNTIME_REQUEST_FAULT_CONTROL_V1";
    /**
     * What application tracing proves about an RPC boundary on its own: the
     * two endpoints named one exchange and one delivery of it was observed.
     */
    public static final String TRACED_EXCHANGE_AUTHORITY =
            "TRACED_RPC_EXCHANGE_CORRELATION_V1";
    private AutomaticRegionEdge() {
    }

    /** Whether one edge is a candidate delivery the trace correlated. */
    public static boolean tracedExchangeCandidate(JsonObject edge) {
        if (edge == null
                || optionalInteger(edge, "schemaVersion", -1) != 3
                || !RUNTIME_PROTOCOL_EDGE_KIND.equals(optionalString(edge, "kind"))
                || optionalString(edge, "fromOccurrenceId").isEmpty()
                || optionalString(edge, "toOccurrenceId").isEmpty()
                || optionalString(edge, "fromOutputPort").isEmpty()
                || optionalString(edge, "toInputPort").isEmpty()
                || !TRACED_EXCHANGE_AUTHORITY.equals(firstNonBlank(
                optionalString(edge, "correlationAuthority"),
                optionalString(edge, "authority")))) {
            return false;
        }
        return true;
    }


    /** One observed shared-location relation used only to link replays. */
    public static boolean sharedLocationCandidate(JsonObject edge) {
        return edge != null
                && optionalInteger(edge, "schemaVersion", -1) == 3
                && "RUNTIME_FIELD_FLOW".equals(optionalString(edge, "kind"))
                && !optionalString(edge, "fromOccurrenceId").isEmpty()
                && !optionalString(edge, "toOccurrenceId").isEmpty()
                && !optionalString(edge, "fromOutputPort").isEmpty()
                && !optionalString(edge, "toInputPort").isEmpty()
                && !optionalString(edge, SharedFieldFlow.EDGE_LOCATION).isEmpty()
                && SharedFieldFlow.LOCATION_MATCH_AUTHORITY.equals(
                firstNonBlank(optionalString(edge, "correlationAuthority"),
                        optionalString(edge, "authority")));
    }

    /**
     * A scheduling-only control predecessor.  It deliberately names no value
     * ports: the marker is an independent symbolic input, while the exact
     * request/response transaction supplies the causal membership proof.
     */
    public static boolean trustedRequestFaultControl(JsonObject edge) {
        if (edge == null
                || optionalInteger(edge, "schemaVersion", -1) != 3
                || !RUNTIME_REQUEST_CONTROL_EDGE_KIND.equals(
                optionalString(edge, "kind"))
                || !EXACT_REQUEST_FAULT_CONTROL_AUTHORITY.equals(
                firstNonBlank(optionalString(edge, "correlationAuthority"),
                        optionalString(edge, "authority")))
                || optionalString(edge, "fromOccurrenceId").isEmpty()
                || optionalString(edge, "toOccurrenceId").isEmpty()
                || optionalString(edge, "sourceKey").isEmpty()
                || OccurrenceBinding.UNREGISTERED_SOURCE_KEY.equals(
                optionalString(edge, "sourceKey"))
                || !optionalString(edge, "sourceKey").equals(
                optionalString(edge, "consumerSourceKey"))
                || optionalString(edge, "requestKey").isEmpty()
                || optionalString(edge, "exchangeTransaction").isEmpty()
                || optionalString(edge, "faultPortId").isEmpty()
                || optionalString(edge, "symbolicName").isEmpty()
                || optionalString(edge, "controlledResponseEdgeId").isEmpty()
                || !"CONCRETE_STRUCTURE_CARRIER".equals(
                optionalString(edge, "dependencyRole"))) {
            return false;
        }
        long fault = optionalLongInteger(edge, "faultEventSeq", -1L);
        long requestSend = optionalLongInteger(edge, "requestSenderEventSeq", -1L);
        long requestReceive = optionalLongInteger(edge,
                "requestReceiverEventSeq", -1L);
        long responseSend = optionalLongInteger(edge,
                "responseSenderEventSeq", -1L);
        long responseReceive = optionalLongInteger(edge,
                "responseReceiverEventSeq", -1L);
        return fault >= 0L && requestSend >= 0L
                && requestSend < fault
                && fault < requestReceive
                && requestSend < requestReceive
                && requestReceive < responseSend
                && responseSend < responseReceive;
    }

}
