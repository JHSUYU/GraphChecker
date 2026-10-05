package edu.uva.liftlab.graphchecker.plan;

import edu.uva.liftlab.graphchecker.causynth.MapFields;

import java.nio.charset.StandardCharsets;
import java.util.Map;
import java.util.UUID;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;

/** Static catalog of the values messages carry, their typed ports and the
 *  gaps discovery could not resolve.  A port is one carried value -- a
 *  message field or a declared row -- with
 *  every capture that writes it and every capture that reads it; direction
 *  and transport are no part of it
 *  (the recording binds each capture to its exchange).  {@link
 *  #EXCHANGE_SITE_KEY} is the static identity of a port, never a runtime
 *  exchange. */
public final class CommunicationCatalogContract {

    /** Bump whenever a field is added, removed or re-interpreted. */
    public static final int SCHEMA_VERSION = 5;

    public static final String SCHEMA_VERSION_FIELD = "schemaVersion";
    public static final String KIND = "kind";

    public static final String CALL_SITE_ID = "callSiteId";
    public static final String EXCHANGE_SITE_KEY = "exchangeSiteKey";
    public static final String TRANSPORT = "transport";
    public static final String DECLARED_CALLEE = "declaredCallee";
    public static final String PORT_ID = "portId";
    public static final String PORT_NAME = "name";
    /** A port row's captures: those that write it, those that read it. */
    public static final String PORT_PRODUCERS = "producers";
    public static final String PORT_CONSUMERS = "consumers";
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

    // Discovery never guesses: what it cannot resolve becomes a gap row.

    /** The row's class, BLOCKING or DIAGNOSTIC, as a GapRow states it. */
    public static final String GAP_CLASS = "cls";
    public static final String GAP_REASON = "reason";
    public static final String GAP_SITE_ID = SiteId.MEMBER;
    public static final String GAP_METHOD = "method";
    public static final String GAP_DETAIL = "detail";

    private CommunicationCatalogContract() {
    }

    /** Static key of one port, never one exchange: {@code port} is its
     *  identity (a message field, or a declared row's id). */
    public static String exchangeSiteKey(String port) {
        String identity = SCHEMA_VERSION + "\n" + nonNull(port);
        return "XCH." + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8));
    }

    /** {@code <exchangeSiteKey>.wire.<name>}. */
    public static String portId(String exchangeSiteKey, String name) {
        return nonNull(exchangeSiteKey) + WIRE + nonNull(name);
    }

    private static final String WIRE = ".wire.";

    /** Whether {@code portId} is an exchange site key + .wire.NAME. */
    public static boolean declaredPortId(String portId) {
        String value = nonNull(portId);
        int suffix = exchangeSiteKeyLength(value);
        return suffix >= 0 && value.startsWith(WIRE, suffix)
                && value.length() > suffix + WIRE.length();
    }

    /**
     * One capture of one port on one side.  A port may have several
     * captures on one side in one region, so this -- never the port id
     * alone -- is what declares a capture once.
     */
    public static String captureKey(String side, Map<String, ?> capture) {
        return side + "\n" + MapFields.text(capture.get(PORT_ID)) + "\n"
                + MapFields.text(capture.get(CALL_SITE_ID)) + "\n"
                + MapFields.text(capture.get(PORT_OUTPUT_CAPTURE_KIND)) + "\n"
                + MapFields.text(capture.get(PORT_ARGUMENT_INDEX));
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
