package edu.uva.liftlab.graphchecker.contract;

import java.nio.charset.StandardCharsets;
import java.util.UUID;

/**
 * The static catalog of communication call sites, their typed ports and the
 * gaps discovery could not resolve.
 *
 * <p>This is the surviving half of static communication discovery.  A region
 * is coarse: it begins at a selected execution-context entry and includes the
 * selected nested calls executed in that context, and a synchronous call does
 * not split it.  A call site is therefore one typed <em>event site</em> inside
 * a region template, never a cut that produces two CFG fragments, so this
 * contract names sites and ports and nothing about fragment identity.</p>
 *
 * <h2>Identity</h2>
 *
 * <p>{@link #EXCHANGE_SITE_KEY} is the pure static identity of one
 * communication <i>site pair</i> - a client call site plus the resolved server
 * entry.  It is not a runtime exchange: that names one concrete attempt and
 * only the runtime mints it.  The static key is the join column the runtime
 * stamps its own provenance against; it is never a second pairing protocol,
 * because a value that crossed the boundary is named by the VM's own
 * export/attach handoff and its {@code VALUE_HANDOFF} ledger edge.</p>
 */
public final class CommunicationCatalogContract {

    /** Bump whenever a field is added, removed or re-interpreted. */
    public static final int SCHEMA_VERSION = 4;

    // ------------------------------------------------------------------
    // Row kinds
    // ------------------------------------------------------------------

    /** {@code kind} of a communication call-site row. */
    public static final String CALL_SITE_ROW_KIND =
            "COMMUNICATION_CALL_SITE";
    /** {@code kind} of a named discovery gap row. */
    public static final String GAP_ROW_KIND = "COMMUNICATION_GAP";

    // ------------------------------------------------------------------
    // Shared field names
    // ------------------------------------------------------------------

    public static final String SCHEMA_VERSION_FIELD = "schemaVersion";
    public static final String KIND = "kind";

    // ------------------------------------------------------------------
    // Call-site row
    // ------------------------------------------------------------------

    /** Stable site id of the client call: {@code <method>#u<unitIndex>}. */
    public static final String CALL_SITE_ID = "callSiteId";
    /** Static identity of the site pair; see {@link #EXCHANGE_SITE_KEY}. */
    public static final String EXCHANGE_SITE_KEY = "exchangeSiteKey";
    /** Adapter that recognised the site, e.g. {@code HADOOP}. */
    public static final String ADAPTER = "adapter";
    /** {@link #TRANSPORT_HADOOP_IPC} or {@link #TRANSPORT_SASL_HANDSHAKE}. */
    public static final String TRANSPORT = "transport";
    /** Protocol identity, e.g. the Hadoop IPC protocol interface name. */
    public static final String PROTOCOL = "protocol";
    /** Method that contains the client call. */
    public static final String CLIENT_METHOD = "clientMethod";
    /** Jimple unit index of the call inside {@link #CLIENT_METHOD}. */
    public static final String CLIENT_UNIT_INDEX = "clientUnitIndex";
    /** Callee signature as declared at the call site. */
    public static final String DECLARED_CALLEE = "declaredCallee";
    /**
     * Post-deserialization semantic server entry, when discovery resolved
     * exactly one.
     *
     * <p>Empty when the slice offers several compatible entries for the same
     * site.  That is not a licence to pick one: the candidates are listed in
     * the accompanying {@link #GAP_SERVER_CUT_UNRESOLVED} row.</p>
     */
    public static final String SERVER_ENTRY_METHOD = "serverEntryMethod";
    /**
     * Every semantic server entry this call site may reach.  Exactly the same
     * list whether or not {@link #SERVER_ENTRY_METHOD} resolved; one element
     * means it did.
     *
     * <p>This is a closed static over-approximation - "these and no others" -
     * and that is a fact discovery really established, so publishing it is a
     * bound rather than a guess.  Nothing here chooses: call order, payload
     * equality and a static endpoint match prove nothing.</p>
     */
    public static final String SERVER_ENTRY_CANDIDATES =
            "serverEntryCandidates";
    /** True when the call carries a response back to its caller. */
    public static final String EXPECTS_RESPONSE = "expectsResponse";
    /** Declared request ports; see the port record below. */
    public static final String REQUEST_PORTS = "requestPorts";
    /** Declared response port, absent when {@link #EXPECTS_RESPONSE}. */
    public static final String RESPONSE_PORT = "responsePort";
    /** Selected primitive leaves carried inside {@link #RESPONSE_PORT}. */
    public static final String RESPONSE_COMPONENT_PORTS =
            "responseComponentPorts";

    public static final String TRANSPORT_HADOOP_IPC = "HADOOP_IPC";
    public static final String TRANSPORT_SASL_HANDSHAKE = "SASL_HANDSHAKE";

    // ------------------------------------------------------------------
    // Port record (request and response)
    // ------------------------------------------------------------------

    /** Stable port identity the runtime binds an expression to. */
    public static final String PORT_ID = "portId";
    /** REQUEST or RESPONSE. */
    public static final String PORT_DIRECTION = "direction";
    /** Human-readable port name; unique inside its call site. */
    public static final String PORT_NAME = "name";
    /** Erased Java type of the value the port carries. */
    public static final String PORT_JAVA_TYPE = "javaType";
    /** Client argument index of a REQUEST port. */
    public static final String PORT_CLIENT_ARGUMENT_INDEX =
            "clientArgumentIndex";
    /** Server parameter index of a REQUEST port. */
    public static final String PORT_SERVER_PARAMETER_INDEX =
            "serverParameterIndex";
    /**
     * The REQUEST port this one is a component of, or absent.
     *
     * <p>A component port is a leaf that crosses <em>inside</em> another
     * port's value rather than as an argument of its own.  The HDFS
     * data-transfer handshake is the case: the client flattens {@code keyId},
     * {@code blockPoolId} and the nonce into one SASL user name and the server
     * parses them back out, so the call carries one string argument and three
     * declared leaves.  Its {@link #PORT_CLIENT_ARGUMENT_INDEX} and
     * {@link #PORT_SERVER_PARAMETER_INDEX} are {@code -1}: it corresponds to
     * no parameter position on either side.</p>
     */
    public static final String PORT_COMPONENT_OF = "componentOfPortId";
    /**
     * Who states the encoding a component port crosses.  The model does not
     * execute that encoding symbolically; this names whoever asserts it.
     */
    public static final String PORT_ENCODING_AUTHORITY = "encodingAuthority";
    /**
     * Exact leaf path the runtime handoff broker addresses a component by.
     * Distinct from {@link #PORT_NAME}: wire adapters may namespace a leaf
     * (for example {@code HANDSHAKE/keyId}).
     */
    public static final String PORT_HANDOFF_LEAF_PATH = "handoffLeafPath";
    /**
     * Canonical structural path from a response object to one selected leaf.
     * Every step is either an exact field declaration or a unique runtime
     * array-element type.  Accessor syntax is lowered to this form at
     * configuration load time; runtime never invokes a configured getter.
     */
    public static final String PORT_HANDOFF_PATH = "handoffPath";
    /** Export-side storage used by a transport adapter's manual VM handoff. */
    public static final String PORT_EXPORT_CARRIER_CLASS =
            "exportCarrierClass";
    public static final String PORT_EXPORT_CARRIER_FIELD =
            "exportCarrierField";
    public static final String PORT_EXPORT_CARRIER_DESCRIPTOR =
            "exportCarrierDescriptor";
    /** Attach-side storage used by a transport adapter's manual VM handoff. */
    public static final String PORT_ATTACH_CARRIER_CLASS =
            "attachCarrierClass";
    public static final String PORT_ATTACH_CARRIER_FIELD =
            "attachCarrierField";
    public static final String PORT_ATTACH_CARRIER_DESCRIPTOR =
            "attachCarrierDescriptor";
    /** Role-local carrier address copied onto a region/task declaration. */
    public static final String PORT_MANUAL_CARRIER_CLASS =
            "manualCarrierClass";
    public static final String PORT_MANUAL_CARRIER_FIELD =
            "manualCarrierField";
    public static final String PORT_MANUAL_CARRIER_DESCRIPTOR =
            "manualCarrierDescriptor";
    /**
     * Leaf path of the one response a cut carries, matching the {@code .resp}
     * suffix {@link #responsePortId} mints.  A request port's leaf path is its
     * own {@link #PORT_NAME}, or the namespaced path a wire adapter declared
     * for a component.
     */
    public static final String RESPONSE_LEAF_PATH = "resp";
    /**
     * Capture kind of a port whose value is read at a call site rather than
     * out of the heap; see {@link #PORT_ARGUMENT_INDEX}.
     */
    public static final String PORT_OUTPUT_CAPTURE_KIND =
            "outputCaptureKind";
    /** {@link #PORT_OUTPUT_CAPTURE_KIND} of a call-argument port. */
    public static final String CAPTURE_CALL_ARGUMENT = "CALL_ARGUMENT";
    /**
     * Capture kind of a response port read as the call's return value:
     * {@code Resp_in}, in the caller's own frame at the call unit.
     */
    public static final String CAPTURE_CALL_RETURN = "CALL_RETURN";
    /**
     * Capture kind of a request port read as the server entry's parameter:
     * {@code Req_in}, one frame above the delivery.  Its position is carried
     * by {@link #PORT_ARGUMENT_INDEX}, the same field the client's
     * call-argument capture uses, so one name means "the argument position of
     * this port's value inside its definition method" on both sides.
     */
    public static final String CAPTURE_ENTRY_PARAMETER = "ENTRY_PARAMETER";
    /**
     * Capture kind of a response port written as the server entry's returned
     * value: {@code Resp_out}.
     */
    public static final String CAPTURE_ENTRY_RETURN = "ENTRY_RETURN";
    /** Argument position a {@link #CAPTURE_CALL_ARGUMENT} port is read at. */
    public static final String PORT_ARGUMENT_INDEX = "argumentIndex";
    /** Method holding the site a call-argument port is captured at. */
    public static final String PORT_DEFINITION_METHOD = "definitionMethod";
    /** Unit index of that site inside {@link #PORT_DEFINITION_METHOD}. */
    public static final String PORT_DEFINITION_UNIT_INDEX =
            "definitionUnitIndex";

    public static final String DIRECTION_REQUEST = "REQUEST";
    public static final String DIRECTION_RESPONSE = "RESPONSE";

    // ------------------------------------------------------------------
    // Named gaps.  Discovery never guesses: anything it cannot resolve
    // statically becomes one of these rows and no call-site or port row.
    // ------------------------------------------------------------------

    /** {@code kind} field of every gap row. */
    public static final String GAP_KIND = "gapKind";
    public static final String GAP_REASON = "reason";
    public static final String GAP_SITE_ID = "siteId";
    public static final String GAP_METHOD = "method";
    public static final String GAP_DETAIL = "detail";

    /**
     * A call site that may hide a communication call but cannot be resolved
     * statically: reflective dispatch, a dynamic proxy, or an unresolvable
     * translator.
     */
    public static final String GAP_CALL_SITE_UNRESOLVED =
            "COMMUNICATION_CALL_SITE_UNRESOLVED";
    /**
     * A recognised protocol call whose post-deserialization server entry has
     * no unique non-transport implementation.
     */
    public static final String GAP_SERVER_CUT_UNRESOLVED =
            "COMMUNICATION_SERVER_CUT_UNRESOLVED";
    /** A resolved server entry whose Jimple body is not available. */
    public static final String GAP_SERVER_BODY_UNAVAILABLE =
            "COMMUNICATION_SERVER_BODY_UNAVAILABLE";
    /** A request port whose client/server correspondence is not unique. */
    public static final String GAP_REQUEST_PORT_UNRESOLVED =
            "COMMUNICATION_REQUEST_PORT_UNRESOLVED";
    private CommunicationCatalogContract() {
    }

    /**
     * Derives the static {@link #EXCHANGE_SITE_KEY} of one client call site
     * and its resolved server entry.  This names the site pair, never one
     * attempt.
     */
    public static String exchangeSiteKey(String transport, String protocol,
                                         String clientCallSiteId,
                                         String declaredCallee,
                                         String serverEntryMethod) {
        String identity = SCHEMA_VERSION + "\n" + text(transport) + "\n"
                + text(protocol) + "\n" + text(clientCallSiteId) + "\n"
                + text(declaredCallee) + "\n" + text(serverEntryMethod);
        return "XCH." + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8));
    }

    /** {@code <method>#u<unitIndex>}: the project-wide site id form. */
    public static String siteId(String method, int unitIndex) {
        return text(method) + "#u" + unitIndex;
    }

    /** {@code <method>#entry}: the site id of a method's first unit. */
    public static String entrySiteId(String method) {
        return text(method) + "#entry";
    }

    /** {@code <exchangeSiteKey>.req.<name>}. */
    public static String requestPortId(String exchangeSiteKey, String name) {
        return text(exchangeSiteKey) + ".req." + text(name);
    }

    /** {@code <exchangeSiteKey>.resp}. */
    public static String responsePortId(String exchangeSiteKey) {
        return text(exchangeSiteKey) + ".resp";
    }

    /** {@code <exchangeSiteKey>.resp.<name>}. */
    public static String responseComponentPortId(String exchangeSiteKey,
                                                 String name) {
        return responsePortId(exchangeSiteKey) + "." + text(name);
    }

    /**
     * True for a port id this contract mints, and only for those.
     *
     * <p>Consumers that have to tell a declared communication port from a
     * run-local symbol cannot do it by shape: such a port is named after its
     * exchange <em>site</em> ({@code <exchangeSiteKey>.req.<name>} or
     * {@code .resp}) and carries no region id, so the {@code <regionId>.in./
     * .out.} test that recognises a region-minted port says nothing about it.
     * This asks the minter instead.</p>
     */
    public static boolean declaredPortId(String portId) {
        String value = text(portId);
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
     * Length of the leading {@link #exchangeSiteKey}, or {@code -1}.  The key
     * is {@code "XCH."} plus one canonical UUID, exactly as
     * {@link #exchangeSiteKey} writes it.
     */
    private static int exchangeSiteKeyLength(String value) {
        String prefix = "XCH.";
        int end = prefix.length() + 36;
        if (!value.startsWith(prefix) || value.length() <= end) return -1;
        String uuid = value.substring(prefix.length(), end);
        try {
            // fromString accepts abbreviated groups, so the canonical form
            // has to agree with what was parsed.
            return UUID.fromString(uuid).toString().equals(uuid) ? end : -1;
        } catch (RuntimeException malformed) {
            return -1;
        }
    }

    private static String text(String value) {
        return value == null ? "" : value;
    }
}
