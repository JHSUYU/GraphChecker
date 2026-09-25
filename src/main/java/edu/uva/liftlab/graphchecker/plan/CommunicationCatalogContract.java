package edu.uva.liftlab.graphchecker.plan;

import java.nio.charset.StandardCharsets;
import java.util.UUID;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;

/** Static catalog of communication call sites, their typed ports and the gaps
 *  discovery could not resolve. A call site is one typed event site inside a
 *  coarse region; this says nothing about fragment identity. {@link
 *  #EXCHANGE_SITE_KEY} is the static identity of a site pair (the join column
 *  for runtime provenance), never a runtime exchange. */
public final class CommunicationCatalogContract {

    /** Bump whenever a field is added, removed or re-interpreted. */
    public static final int SCHEMA_VERSION = 4;

    public static final String SCHEMA_VERSION_FIELD = "schemaVersion";
    public static final String KIND = "kind";

    public static final String CALL_SITE_ID = "callSiteId";
    public static final String EXCHANGE_SITE_KEY = "exchangeSiteKey";
    public static final String TRANSPORT = "transport";
    public static final String CLIENT_METHOD = "clientMethod";
    public static final String DECLARED_CALLEE = "declaredCallee";
    public static final String SERVER_ENTRY_METHOD = "serverEntryMethod";
    public static final String PORT_ID = "portId";
    public static final String PORT_DIRECTION = "direction";
    public static final String PORT_NAME = "name";
    public static final String PORT_JAVA_TYPE = "javaType";
    /** Leaf path the handoff broker addresses (may differ from the name). */
    public static final String PORT_HANDOFF_LEAF_PATH = "handoffLeafPath";
    /** Capture kind of a call-site port; see {@link #PORT_ARGUMENT_INDEX}. */
    public static final String PORT_OUTPUT_CAPTURE_KIND =
            "outputCaptureKind";
    public static final String CAPTURE_CALL_ARGUMENT = "CALL_ARGUMENT";
    /** Response read as the call's return value, in the caller's frame. */
    public static final String CAPTURE_CALL_RETURN = "CALL_RETURN";
    public static final String CAPTURE_METHOD_PARAMETER = "METHOD_PARAMETER";
    public static final String CAPTURE_METHOD_RETURN = "METHOD_RETURN";
    public static final String PORT_ARGUMENT_INDEX = "argumentIndex";
    public static final String PORT_DEFINITION_METHOD = "definitionMethod";
    /** Method whose one call builds a value of the port; absent = RPC. */
    public static final String PORT_FRAME_METHOD = "frameMethod";
    public static final String PORT_DEFINITION_UNIT_INDEX =
            "definitionUnitIndex";

    public static final String DIRECTION_REQUEST = "REQUEST";
    public static final String DIRECTION_RESPONSE = "RESPONSE";

    // Discovery never guesses: what it cannot resolve becomes a gap row.

    /** The row's class, BLOCKING or DIAGNOSTIC, as a GapRow states it. */
    public static final String GAP_CLASS = "cls";
    public static final String GAP_REASON = "reason";
    public static final String GAP_SITE_ID = SiteId.MEMBER;
    public static final String GAP_METHOD = "method";
    public static final String GAP_DETAIL = "detail";

    private CommunicationCatalogContract() {
    }

    /** Static key of a client call site + server entry, never one attempt. */
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

    /** Whether {@code portId} is key + .resp, .resp.NAME or .req.NAME. */
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

    /** Length of the leading {@code "XCH." + canonical UUID}, or -1. */
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
