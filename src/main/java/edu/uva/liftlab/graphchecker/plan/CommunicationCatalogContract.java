package edu.uva.liftlab.graphchecker.plan;

import edu.uva.liftlab.graphchecker.causynth.MapFields;

import java.nio.charset.StandardCharsets;
import java.util.Map;
import java.util.UUID;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;

public final class CommunicationCatalogContract {

    public static final int SCHEMA_VERSION = 5;

    public static final String SCHEMA_VERSION_FIELD = "schemaVersion";
    public static final String KIND = "kind";

    public static final String CALL_SITE_ID = "callSiteId";
    public static final String EXCHANGE_SITE_KEY = "exchangeSiteKey";
    public static final String TRANSPORT = "transport";
    public static final String DECLARED_CALLEE = "declaredCallee";
    public static final String PORT_ID = "portId";
    public static final String PORT_NAME = "name";
    public static final String PORT_PRODUCERS = "producers";
    public static final String PORT_CONSUMERS = "consumers";
    public static final String PORT_JAVA_TYPE = "javaType";
    public static final String PORT_HANDOFF_LEAF_PATH = "handoffLeafPath";
    public static final String PORT_OUTPUT_CAPTURE_KIND =
            "outputCaptureKind";
    public static final String CAPTURE_CALL_ARGUMENT = "CALL_ARGUMENT";
    public static final String CAPTURE_CALL_RETURN = "CALL_RETURN";
    public static final String CAPTURE_METHOD_PARAMETER = "METHOD_PARAMETER";
    public static final String CAPTURE_METHOD_RETURN = "METHOD_RETURN";
    public static final String PORT_ARGUMENT_INDEX = "argumentIndex";
    public static final String PORT_DEFINITION_METHOD = "definitionMethod";
    public static final String PORT_CODEC_FIELD = "codecField";
    public static final String PORT_DEFINITION_UNIT_INDEX =
            "definitionUnitIndex";


    public static final String GAP_CLASS = "cls";
    public static final String GAP_REASON = "reason";
    public static final String GAP_SITE_ID = SiteId.MEMBER;
    public static final String GAP_METHOD = "method";
    public static final String GAP_DETAIL = "detail";

    private CommunicationCatalogContract() {
    }

    public static String exchangeSiteKey(String port) {
        String identity = SCHEMA_VERSION + "\n" + nonNull(port);
        return "XCH." + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8));
    }

    public static String portId(String exchangeSiteKey, String name) {
        return nonNull(exchangeSiteKey) + WIRE + nonNull(name);
    }

    private static final String WIRE = ".wire.";

    public static boolean declaredPortId(String portId) {
        String value = nonNull(portId);
        int suffix = exchangeSiteKeyLength(value);
        return suffix >= 0 && value.startsWith(WIRE, suffix)
                && value.length() > suffix + WIRE.length();
    }

    public static String captureKey(String side, Map<String, ?> capture) {
        return side + "\n" + MapFields.text(capture.get(PORT_ID)) + "\n"
                + MapFields.text(capture.get(CALL_SITE_ID)) + "\n"
                + MapFields.text(capture.get(PORT_OUTPUT_CAPTURE_KIND)) + "\n"
                + MapFields.text(capture.get(PORT_ARGUMENT_INDEX));
    }

    private static int exchangeSiteKeyLength(String value) {
        String prefix = "XCH.";
        int end = prefix.length() + 36;
        if (!value.startsWith(prefix) || value.length() <= end) return -1;
        String uuid = value.substring(prefix.length(), end);
        try {
            return UUID.fromString(uuid).toString().equals(uuid) ? end : -1;
        } catch (RuntimeException malformed) {
            return -1;
        }
    }
}
