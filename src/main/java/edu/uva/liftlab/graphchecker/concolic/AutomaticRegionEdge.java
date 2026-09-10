package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.runtime.OccurrenceMinter;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;

/** Evidence gate shared by graph discovery and SMT preparation. */
public final class AutomaticRegionEdge {
    static final String RUNTIME_PROTOCOL_EDGE_KIND =
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
                || integer(edge, "schemaVersion", -1) != 3
                || !RUNTIME_PROTOCOL_EDGE_KIND.equals(string(edge, "kind"))
                || string(edge, "fromOccurrenceId").isEmpty()
                || string(edge, "toOccurrenceId").isEmpty()
                || string(edge, "fromOutputPort").isEmpty()
                || string(edge, "toInputPort").isEmpty()
                || !TRACED_EXCHANGE_AUTHORITY.equals(firstNonBlank(
                string(edge, "correlationAuthority"),
                string(edge, "authority")))) {
            return false;
        }
        return true;
    }


    /** One observed shared-location relation used only to link replays. */
    public static boolean sharedLocationCandidate(JsonObject edge) {
        return edge != null
                && integer(edge, "schemaVersion", -1) == 3
                && "RUNTIME_FIELD_FLOW".equals(string(edge, "kind"))
                && !string(edge, "fromOccurrenceId").isEmpty()
                && !string(edge, "toOccurrenceId").isEmpty()
                && !string(edge, "fromOutputPort").isEmpty()
                && !string(edge, "toInputPort").isEmpty()
                && !string(edge, SharedFieldFlow.EDGE_LOCATION).isEmpty()
                && SharedFieldFlow.LOCATION_MATCH_AUTHORITY.equals(
                firstNonBlank(string(edge, "correlationAuthority"),
                        string(edge, "authority")));
    }

    /** Evidence that may select the two recorded interaction summaries. */
    public static boolean summaryTraversalBinding(JsonObject binding) {
        return tracedExchangeCandidate(binding)
                || sharedLocationCandidate(binding)
                || trustedRequestFaultControl(binding);
    }

    /**
     * A scheduling-only control predecessor.  It deliberately names no value
     * ports: the marker is an independent symbolic input, while the exact
     * request/response transaction supplies the causal membership proof.
     */
    public static boolean trustedRequestFaultControl(JsonObject edge) {
        if (edge == null
                || integer(edge, "schemaVersion", -1) != 3
                || !RUNTIME_REQUEST_CONTROL_EDGE_KIND.equals(
                string(edge, "kind"))
                || !EXACT_REQUEST_FAULT_CONTROL_AUTHORITY.equals(
                firstNonBlank(string(edge, "correlationAuthority"),
                        string(edge, "authority")))
                || string(edge, "fromOccurrenceId").isEmpty()
                || string(edge, "toOccurrenceId").isEmpty()
                || string(edge, "sourceKey").isEmpty()
                || OccurrenceMinter.UNREGISTERED_SOURCE_KEY.equals(
                string(edge, "sourceKey"))
                || !string(edge, "sourceKey").equals(
                string(edge, "consumerSourceKey"))
                || string(edge, "requestKey").isEmpty()
                || string(edge, "exchangeTransaction").isEmpty()
                || string(edge, "faultPortId").isEmpty()
                || string(edge, "symbolicName").isEmpty()
                || string(edge, "controlledResponseEdgeId").isEmpty()
                || !"CONCRETE_STRUCTURE_CARRIER".equals(
                string(edge, "dependencyRole"))) {
            return false;
        }
        long fault = longInteger(edge, "faultEventSeq", -1L);
        long requestSend = longInteger(edge, "requestSenderEventSeq", -1L);
        long requestReceive = longInteger(edge,
                "requestReceiverEventSeq", -1L);
        long responseSend = longInteger(edge,
                "responseSenderEventSeq", -1L);
        long responseReceive = longInteger(edge,
                "responseReceiverEventSeq", -1L);
        return fault >= 0L && requestSend >= 0L
                && requestSend < fault
                && fault < requestReceive
                && requestSend < requestReceive
                && requestReceive < responseSend
                && responseSend < responseReceive;
    }

}
