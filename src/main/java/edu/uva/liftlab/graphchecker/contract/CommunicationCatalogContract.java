package edu.uva.liftlab.graphchecker.contract;

import java.nio.charset.StandardCharsets;
import java.util.UUID;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.nonNull;

/**
 * The static catalog of communication call sites, their typed ports and the
 * gaps discovery could not resolve.  A region is coarse and a synchronous
 * call does not split it, so a call site is one typed event site inside a
 * region template and this contract says nothing about fragment identity.
 *
 * <p>{@link #EXCHANGE_SITE_KEY} is the pure static identity of one site pair
 * and never a runtime exchange: it is the join column the runtime stamps
 * provenance against, not a second pairing protocol.  A value that crossed
 * the boundary is named by the VM's own {@code VALUE_HANDOFF} edge.</p>
 */
public final class CommunicationCatalogContract {

    /** Bump whenever a field is added, removed or re-interpreted. */
    public static final int SCHEMA_VERSION = 4;

    public static final String CALL_SITE_ROW_KIND =
            "COMMUNICATION_CALL_SITE";
    public static final String GAP_ROW_KIND = "COMMUNICATION_GAP";

    public static final String SCHEMA_VERSION_FIELD = "schemaVersion";
    public static final String KIND = "kind";

    /** Stable site id of the client call: {@code <method>#u<unitIndex>}. */
    public static final String CALL_SITE_ID = "callSiteId";
    public static final String EXCHANGE_SITE_KEY = "exchangeSiteKey";
    public static final String ADAPTER = "adapter";
    /** {@link #TRANSPORT_HADOOP_IPC} or {@link #TRANSPORT_SASL_HANDSHAKE}. */
    public static final String TRANSPORT = "transport";
    public static final String PROTOCOL = "protocol";
    public static final String CLIENT_METHOD = "clientMethod";
    public static final String CLIENT_UNIT_INDEX = "clientUnitIndex";
    public static final String DECLARED_CALLEE = "declaredCallee";
    /** Post-deserialization semantic server entry when discovery resolved
     *  exactly one.  Empty is not a licence to pick one: the candidates are
     *  in the accompanying {@link #GAP_SERVER_CUT_UNRESOLVED} row. */
    public static final String SERVER_ENTRY_METHOD = "serverEntryMethod";
    /** Every semantic server entry this call site may reach; one element
     *  means {@link #SERVER_ENTRY_METHOD} resolved.  A closed static
     *  over-approximation, so publishing it is a bound rather than a guess -
     *  nothing here chooses. */
    public static final String SERVER_ENTRY_CANDIDATES =
            "serverEntryCandidates";
    public static final String EXPECTS_RESPONSE = "expectsResponse";
    public static final String REQUEST_PORTS = "requestPorts";
    public static final String RESPONSE_PORT = "responsePort";
    public static final String RESPONSE_COMPONENT_PORTS =
            "responseComponentPorts";

    public static final String TRANSPORT_HADOOP_IPC = "HADOOP_IPC";
    public static final String TRANSPORT_SASL_HANDSHAKE = "SASL_HANDSHAKE";

    public static final String PORT_ID = "portId";
    /** REQUEST or RESPONSE. */
    public static final String PORT_DIRECTION = "direction";
    public static final String PORT_NAME = "name";
    public static final String PORT_JAVA_TYPE = "javaType";
    public static final String PORT_CLIENT_ARGUMENT_INDEX =
            "clientArgumentIndex";
    public static final String PORT_SERVER_PARAMETER_INDEX =
            "serverParameterIndex";
    /** The REQUEST port this one is a component of, or absent: a leaf that
     *  crosses <em>inside</em> another port's value.  The HDFS handshake
     *  flattens {@code keyId}, {@code blockPoolId} and the nonce into one SASL
     *  user name, so the call carries one argument and three declared leaves
     *  whose argument/parameter indices are {@code -1}. */
    public static final String PORT_COMPONENT_OF = "componentOfPortId";
    /** Who states the encoding a component port crosses; the model does not
     *  execute that encoding symbolically. */
    public static final String PORT_ENCODING_AUTHORITY = "encodingAuthority";
    /**
     * Exact leaf path the runtime handoff broker addresses a component by.
     * Distinct from {@link #PORT_NAME}: wire adapters may namespace a leaf.
     */
    public static final String PORT_HANDOFF_LEAF_PATH = "handoffLeafPath";
    /** Canonical structural path from a response object to one selected leaf.
     *  Accessor syntax is lowered to this at load time; runtime never invokes
     *  a configured getter. */
    public static final String PORT_HANDOFF_PATH = "handoffPath";
    public static final String PORT_EXPORT_CARRIER_CLASS =
            "exportCarrierClass";
    public static final String PORT_EXPORT_CARRIER_FIELD =
            "exportCarrierField";
    public static final String PORT_EXPORT_CARRIER_DESCRIPTOR =
            "exportCarrierDescriptor";
    public static final String PORT_ATTACH_CARRIER_CLASS =
            "attachCarrierClass";
    public static final String PORT_ATTACH_CARRIER_FIELD =
            "attachCarrierField";
    public static final String PORT_ATTACH_CARRIER_DESCRIPTOR =
            "attachCarrierDescriptor";
    public static final String PORT_MANUAL_CARRIER_CLASS =
            "manualCarrierClass";
    public static final String PORT_MANUAL_CARRIER_FIELD =
            "manualCarrierField";
    public static final String PORT_MANUAL_CARRIER_DESCRIPTOR =
            "manualCarrierDescriptor";
    /**
     * Leaf path of the one response a cut carries, matching the {@code .resp}
     * suffix {@link #responsePortId} mints.
     */
    public static final String RESPONSE_LEAF_PATH = "resp";
    /** Capture kind of a port read at a call site rather than out of the
     *  heap; see {@link #PORT_ARGUMENT_INDEX}. */
    public static final String PORT_OUTPUT_CAPTURE_KIND =
            "outputCaptureKind";
    public static final String CAPTURE_CALL_ARGUMENT = "CALL_ARGUMENT";
    /** Response port read as the call's return value: {@code Resp_in}, in
     *  the caller's own frame at the call unit. */
    public static final String CAPTURE_CALL_RETURN = "CALL_RETURN";
    /** Request port read as the server entry's parameter: {@code Req_in}, one
     *  frame above the delivery.  Its position is
     *  {@link #PORT_ARGUMENT_INDEX}, the same field the client's capture
     *  uses. */
    public static final String CAPTURE_ENTRY_PARAMETER = "ENTRY_PARAMETER";
    /** Response port written as the server entry's returned value:
     *  {@code Resp_out}. */
    public static final String CAPTURE_ENTRY_RETURN = "ENTRY_RETURN";
    public static final String PORT_ARGUMENT_INDEX = "argumentIndex";
    public static final String PORT_DEFINITION_METHOD = "definitionMethod";
    public static final String PORT_DEFINITION_UNIT_INDEX =
            "definitionUnitIndex";

    public static final String DIRECTION_REQUEST = "REQUEST";
    public static final String DIRECTION_RESPONSE = "RESPONSE";

    // Discovery never guesses: anything it cannot resolve statically becomes
    // one of these gap rows and no call-site or port row.

    public static final String GAP_KIND = "gapKind";
    public static final String GAP_REASON = "reason";
    public static final String GAP_SITE_ID = "siteId";
    public static final String GAP_METHOD = "method";
    public static final String GAP_DETAIL = "detail";

    /** Derives the static {@link #EXCHANGE_SITE_KEY} of one client call site
     *  and its resolved server entry; names the site pair, never one
     *  attempt. */
    public static final String GAP_CALL_SITE_UNRESOLVED =
            "COMMUNICATION_CALL_SITE_UNRESOLVED";
    /**
     * A recognised protocol call whose post-deserialization server entry has
     * no unique non-transport implementation.
     */
    public static final String GAP_SERVER_CUT_UNRESOLVED =
            "COMMUNICATION_SERVER_CUT_UNRESOLVED";
    public static final String GAP_SERVER_BODY_UNAVAILABLE =
            "COMMUNICATION_SERVER_BODY_UNAVAILABLE";
    public static final String GAP_REQUEST_PORT_UNRESOLVED =
            "COMMUNICATION_REQUEST_PORT_UNRESOLVED";
    private CommunicationCatalogContract() {
    }

    /**
     * Derives the static {@link #EXCHANGE_SITE_KEY} of one client call site
     * and its resolved server entry.  Names the site pair, never one attempt.
     */
    public static String exchangeSiteKey(String transport, String protocol,
                                         String clientCallSiteId,
                                         String declaredCallee,
                                         String serverEntryMethod) {
        String identity = SCHEMA_VERSION + "\n" + nonNull(transport) + "\n"
                + nonNull(protocol) + "\n" + nonNull(clientCallSiteId) + "\n"
                + nonNull(declaredCallee) + "\n" + nonNull(serverEntryMethod);
        return "XCH." + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8));
    }

    /** {@code <method>#u<unitIndex>}: the project-wide site id form. */
    public static String siteId(String method, int unitIndex) {
        return nonNull(method) + "#u" + unitIndex;
    }

    /** {@code <exchangeSiteKey>.req.<name>}. */
    public static String requestPortId(String exchangeSiteKey, String name) {
        return nonNull(exchangeSiteKey) + ".req." + nonNull(name);
    }

    /** {@code <exchangeSiteKey>.resp}. */
    public static String responsePortId(String exchangeSiteKey) {
        return nonNull(exchangeSiteKey) + ".resp";
    }

    /** {@code <exchangeSiteKey>.resp.<name>}. */
    public static String responseComponentPortId(String exchangeSiteKey,
                                                 String name) {
        return responsePortId(exchangeSiteKey) + "." + nonNull(name);
    }

    /** Length of the leading {@link #exchangeSiteKey}, or {@code -1}: the key
     *  is {@code "XCH."} plus one canonical UUID. */
    public static boolean declaredPortId(String portId) {
        String value = nonNull(portId);
        int suffix = exchangeSiteKeyLength(value);
        if (suffix < 0) return false;
        String tail = value.substring(suffix);
        if (tail.equals(".resp")) return true;
        if (tail.startsWith(".resp.")
                && tail.length() > ".resp.".length()) return true;
        return tail.startsWith(".req.")
                && tail.length() > ".req.".length();
    }

    /**
     * Length of the leading {@link #exchangeSiteKey}, or {@code -1}: the key
     * is {@code "XCH."} plus one canonical UUID.
     */
    private static int exchangeSiteKeyLength(String value) {
        String prefix = "XCH.";
        int end = prefix.length() + 36;
        if (!value.startsWith(prefix) || value.length() <= end) return -1;
        String uuid = value.substring(prefix.length(), end);
        try {
            // fromString accepts abbreviated groups.
            return UUID.fromString(uuid).toString().equals(uuid) ? end : -1;
        } catch (RuntimeException malformed) {
            return -1;
        }
    }
}
