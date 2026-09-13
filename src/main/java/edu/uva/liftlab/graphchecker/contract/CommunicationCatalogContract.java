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

    public static final String GAP_ROW_KIND = "COMMUNICATION_GAP";

    public static final String SCHEMA_VERSION_FIELD = "schemaVersion";
    public static final String KIND = "kind";

    /** Stable site id of the client call: {@code <method>#u<unitIndex>}. */
    public static final String CALL_SITE_ID = "callSiteId";
    public static final String EXCHANGE_SITE_KEY = "exchangeSiteKey";
    public static final String TRANSPORT = "transport";
    public static final String CLIENT_METHOD = "clientMethod";
    public static final String DECLARED_CALLEE = "declaredCallee";
    /** Consumer-side method of the declared wire flow. */
    public static final String SERVER_ENTRY_METHOD = "serverEntryMethod";
    /** Consumer-side methods reachable from this static flow. */
    public static final String SERVER_ENTRY_CANDIDATES =
            "serverEntryCandidates";
    public static final String PORT_ID = "portId";
    /** REQUEST or RESPONSE. */
    public static final String PORT_DIRECTION = "direction";
    public static final String PORT_NAME = "name";
    public static final String PORT_JAVA_TYPE = "javaType";
    /**
     * Exact leaf path the runtime handoff broker addresses a component by.
     * Distinct from {@link #PORT_NAME}: wire adapters may namespace a leaf.
     */
    public static final String PORT_HANDOFF_LEAF_PATH = "handoffLeafPath";
    /** Capture kind of a port read at a call site rather than out of the
     *  heap; see {@link #PORT_ARGUMENT_INDEX}. */
    public static final String PORT_OUTPUT_CAPTURE_KIND =
            "outputCaptureKind";
    public static final String CAPTURE_CALL_ARGUMENT = "CALL_ARGUMENT";
    /** Response port read as the call's return value: {@code Resp_in}, in
     *  the caller's own frame at the call unit. */
    public static final String CAPTURE_CALL_RETURN = "CALL_RETURN";
    public static final String CAPTURE_METHOD_PARAMETER = "METHOD_PARAMETER";
    public static final String CAPTURE_METHOD_RETURN = "METHOD_RETURN";
    public static final String PORT_ARGUMENT_INDEX = "argumentIndex";
    public static final String PORT_DEFINITION_METHOD = "definitionMethod";
    /**
     * The method whose one call builds one instance of the value a port
     * belongs to -- the frame leaves of that port are addressed within.
     * Optional: a port that names none is addressed within its RPC message.
     */
    public static final String PORT_FRAME_METHOD = "frameMethod";
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

    /** {@code <exchangeSiteKey>.req.<name>}. */
    public static String requestPortId(String exchangeSiteKey, String name) {
        return nonNull(exchangeSiteKey) + ".req." + nonNull(name);
    }

    /** {@code <exchangeSiteKey>.resp}. */
    public static String responsePortId(String exchangeSiteKey) {
        return nonNull(exchangeSiteKey) + ".resp";
    }

    /** {@code <exchangeSiteKey>.resp.<name>}. */
    public static String namedResponsePortId(String exchangeSiteKey,
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
