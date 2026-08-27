package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

/**
 * One transport-neutral description of a selected communication call site.
 * The generic catalog code in {@link CommunicationCatalogPlanner} consumes
 * only this description; a {@link CommunicationCallSiteAdapter} answers what
 * the protocol is, so protocol knowledge stays out of the discovery
 * algorithm.  One remote call produces exactly one client cut and exactly one
 * server cut; transport, serialization and translator frames between them are
 * implementation sites and never become call sites of their own.
 */
final class CommunicationCallSite {

    /** The method that contains the client cut. */
    final String clientMethod;
    /** Jimple unit index of the client cut inside {@link #clientMethod}. */
    final int clientUnitIndex;
    /** {@code <clientMethod>#u<clientUnitIndex>}. */
    final String cutSiteId;
    /** Static identity of this client/server site pair. */
    final String exchangeSiteKey;
    /** Adapter that recognised the site, e.g. {@code HADOOP}. */
    final String adapter;
    /** {@code HADOOP_IPC} or {@code SASL_HANDSHAKE}. */
    final String transport;
    /** Protocol identity; the Hadoop IPC protocol interface, for example. */
    final String protocol;
    /** Callee signature as declared at the call site. */
    final String declaredCallee;
    /**
     * Post-deserialization semantic entry on the server side, or {@code ""}
     * when {@link #serverEntryCandidates} does not single one out.
     */
    final String serverEntryMethod;
    /**
     * Every semantic server entry this cut may reach - a bound, where
     * {@link #serverEntryMethod} is an answer.  Several means static analysis
     * cannot say which entry this cut delivers to (README section 1: a static
     * endpoint match never proves an RPC edge), so discovery publishes the set
     * it proved rather than guessing a member; the runtime's recorded
     * {@code SEND}/{@code RECEIVE} pair resolves it, and a fragment this list
     * does not name is refused.  The accompanying
     * {@link CommunicationCatalogContract#GAP_SERVER_CUT_UNRESOLVED} row stays
     * either way: an admissible set larger than one is still unresolved.
     */
    final List<String> serverEntryCandidates;
    /** True when a response flows back to the calling frame. */
    final boolean expectsResponse;
    /** Erased Java type of the response, empty when there is none. */
    final String responseJavaType;
    final List<RequestPort> request;
    final List<ResponseComponentPort> responseComponents;
    CommunicationCallSite(String clientMethod, int clientUnitIndex,
                          String adapter, String transport, String protocol,
                          String declaredCallee,
                          List<String> serverEntryCandidates,
                          boolean expectsResponse, String responseJavaType,
                          List<RequestPort> request,
                          List<ResponseComponentPort> responseComponents) {
        this.clientMethod = clientMethod;
        this.clientUnitIndex = clientUnitIndex;
        this.cutSiteId = CommunicationCatalogContract.siteId(clientMethod,
                clientUnitIndex);
        this.adapter = adapter;
        this.transport = transport;
        this.protocol = protocol;
        this.declaredCallee = declaredCallee;
        this.serverEntryCandidates = Collections.unmodifiableList(
                new ArrayList<>(new LinkedHashSet<>(serverEntryCandidates)));
        this.serverEntryMethod = this.serverEntryCandidates.size() == 1
                ? this.serverEntryCandidates.get(0) : "";
        this.expectsResponse = expectsResponse;
        this.responseJavaType = text(responseJavaType);
        this.request = Collections.unmodifiableList(
                new ArrayList<>(request));
        this.responseComponents = Collections.unmodifiableList(
                new ArrayList<>(responseComponents));
        if (!expectsResponse && !this.responseComponents.isEmpty()) {
            throw new IllegalArgumentException(
                    "response components require a response port");
        }
        // Derived only from fields the row itself carries, so the key stays
        // reproducible from the artifact even when the entry is unresolved.
        this.exchangeSiteKey = CommunicationCatalogContract.exchangeSiteKey(
                transport, protocol, cutSiteId, declaredCallee,
                serverEntryMethod);
    }

    /** The identity every declared port row opens with. */
    private static Map<String, Object> portRow(String portId,
                                               String direction, String name,
                                               String javaType) {
        Map<String, Object> port = new LinkedHashMap<>();
        port.put(CommunicationCatalogContract.PORT_ID, portId);
        port.put(CommunicationCatalogContract.PORT_DIRECTION, direction);
        port.put(CommunicationCatalogContract.PORT_NAME, name);
        port.put(CommunicationCatalogContract.PORT_JAVA_TYPE, javaType);
        return port;
    }

    /** One configured semantic leaf inside the response object graph. */
    static final class ResponseComponentPort {
        final String name;
        final String javaType;
        final List<ResponsePathStep> handoffPath;

        ResponseComponentPort(String name, String javaType,
                              List<ResponsePathStep> handoffPath) {
            this.name = name;
            this.javaType = javaType;
            this.handoffPath = Collections.unmodifiableList(
                    new ArrayList<>(handoffPath));
        }

        Map<String, Object> row(String exchangeSiteKey) {
            Map<String, Object> port = portRow(
                    CommunicationCatalogContract.responseComponentPortId(
                            exchangeSiteKey, name),
                    CommunicationCatalogContract.DIRECTION_RESPONSE,
                    name, javaType);
            port.put(CommunicationCatalogContract.PORT_COMPONENT_OF,
                    CommunicationCatalogContract.responsePortId(
                            exchangeSiteKey));
            port.put(CommunicationCatalogContract.PORT_ENCODING_AUTHORITY,
                    "CONFIGURED_RESPONSE_FIELD_PATH_V1");
            List<String> names = new ArrayList<>();
            List<Map<String, Object>> path = new ArrayList<>();
            for (ResponsePathStep step : handoffPath) {
                String segment = step.leafSegment();
                if (segment.isEmpty()) throw new IllegalArgumentException(
                        "response component path is not exact");
                names.add(segment);
                path.add(step.row());
            }
            if (names.isEmpty() || !name.equals(
                    names.get(names.size() - 1))) {
                throw new IllegalArgumentException(
                        "response component must name its exact leaf: "
                                + name);
            }
            port.put(CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH,
                    "resp/" + String.join("/", names));
            port.put(CommunicationCatalogContract.PORT_HANDOFF_PATH, path);
            if (javaType.endsWith("[]")) {
                port.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
                port.put("dependencyRole", "VALUE_FRONTIER");
            }
            return port;
        }
    }

    /** One declared request value crossing the cut. */
    static final class RequestPort {
        final String name;
        final int clientArgumentIndex;
        final int serverParameterIndex;
        final String javaType;
        /** Name of the request port this one is a component of, or {@code ""}:
         *  the HDFS handshake flattens {@code keyId}, {@code blockPoolId} and
         *  {@code nonce} into one SASL user name (README section 3). */
        final String componentOf;
        /** Who states the encoding of a component port. */
        final String encodingAuthority;
        /** Exact leaf path stated by the runtime handoff broker. */
        final String handoffLeafPath;
        /** Exact sender/receiver storage addressed by a manual VM handoff. */
        final String exportCarrierClass;
        final String exportCarrierField;
        final String exportCarrierDescriptor;
        final String attachCarrierClass;
        final String attachCarrierField;
        final String attachCarrierDescriptor;

        RequestPort(String name, int clientArgumentIndex,
                    int serverParameterIndex, String javaType) {
            this(name, clientArgumentIndex, serverParameterIndex, javaType,
                    "", "", "", "", "", "", "", "", "");
        }

        RequestPort(String name, int clientArgumentIndex,
                    int serverParameterIndex, String javaType,
                    String componentOf, String encodingAuthority,
                    String handoffLeafPath,
                    String exportCarrierClass, String exportCarrierField,
                    String exportCarrierDescriptor,
                    String attachCarrierClass, String attachCarrierField,
                    String attachCarrierDescriptor) {
            this.name = name;
            this.clientArgumentIndex = clientArgumentIndex;
            this.serverParameterIndex = serverParameterIndex;
            this.javaType = javaType;
            this.componentOf = text(componentOf);
            this.encodingAuthority = text(encodingAuthority);
            this.handoffLeafPath = text(handoffLeafPath);
            this.exportCarrierClass = text(exportCarrierClass);
            this.exportCarrierField = text(exportCarrierField);
            this.exportCarrierDescriptor = text(exportCarrierDescriptor);
            this.attachCarrierClass = text(attachCarrierClass);
            this.attachCarrierField = text(attachCarrierField);
            this.attachCarrierDescriptor = text(attachCarrierDescriptor);
        }

        Map<String, Object> row(String exchangeSiteKey) {
            Map<String, Object> port = portRow(
                    CommunicationCatalogContract.requestPortId(
                            exchangeSiteKey, name),
                    CommunicationCatalogContract.DIRECTION_REQUEST,
                    name, javaType);
            port.put(CommunicationCatalogContract.PORT_CLIENT_ARGUMENT_INDEX, clientArgumentIndex);
            port.put(CommunicationCatalogContract.PORT_SERVER_PARAMETER_INDEX, serverParameterIndex);
            if (!componentOf.isEmpty()) {
                port.put(CommunicationCatalogContract.PORT_COMPONENT_OF,
                        CommunicationCatalogContract.requestPortId(
                                exchangeSiteKey, componentOf));
                port.put(CommunicationCatalogContract.PORT_ENCODING_AUTHORITY, encodingAuthority);
            }
            // Every declared port names the leaf the broker addresses it by,
            // on both sides of the cut.
            port.put(CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH,
                    handoffLeafPath.isEmpty() ? name : handoffLeafPath);
            putIfComplete(port,
                    CommunicationCatalogContract.PORT_EXPORT_CARRIER_CLASS,
                    CommunicationCatalogContract.PORT_EXPORT_CARRIER_FIELD,
                    CommunicationCatalogContract.PORT_EXPORT_CARRIER_DESCRIPTOR,
                    exportCarrierClass, exportCarrierField,
                    exportCarrierDescriptor);
            putIfComplete(port,
                    CommunicationCatalogContract.PORT_ATTACH_CARRIER_CLASS,
                    CommunicationCatalogContract.PORT_ATTACH_CARRIER_FIELD,
                    CommunicationCatalogContract.PORT_ATTACH_CARRIER_DESCRIPTOR,
                    attachCarrierClass, attachCarrierField,
                    attachCarrierDescriptor);
            return port;
        }

        private static void putIfComplete(Map<String, Object> row,
                                          String classKey, String fieldKey,
                                          String descriptorKey,
                                          String owner, String field,
                                          String descriptor) {
            if (owner.isEmpty() || field.isEmpty() || descriptor.isEmpty()) {
                return;
            }
            row.put(classKey, owner);
            row.put(fieldKey, field);
            row.put(descriptorKey, descriptor);
        }
    }

    /** The call-site (cut) artifact row. */
    Map<String, Object> row() {
        Map<String, Object> row = CommunicationCatalogPlanner.newRow(
                CommunicationCatalogContract.CALL_SITE_ROW_KIND);
        row.put(CommunicationCatalogContract.CALL_SITE_ID, cutSiteId);
        row.put(CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                exchangeSiteKey);
        row.put(CommunicationCatalogContract.ADAPTER, adapter);
        row.put(CommunicationCatalogContract.TRANSPORT, transport);
        row.put(CommunicationCatalogContract.PROTOCOL, protocol);
        row.put(CommunicationCatalogContract.CLIENT_METHOD, clientMethod);
        row.put(CommunicationCatalogContract.CLIENT_UNIT_INDEX,
                clientUnitIndex);
        row.put(CommunicationCatalogContract.DECLARED_CALLEE,
                declaredCallee);
        row.put(CommunicationCatalogContract.SERVER_ENTRY_METHOD,
                serverEntryMethod);
        row.put(CommunicationCatalogContract.SERVER_ENTRY_CANDIDATES,
                new ArrayList<>(serverEntryCandidates));
        row.put(CommunicationCatalogContract.EXPECTS_RESPONSE,
                expectsResponse);
        List<Map<String, Object>> ports = new ArrayList<>();
        for (RequestPort port : request) {
            ports.add(port.row(exchangeSiteKey));
        }
        row.put(CommunicationCatalogContract.REQUEST_PORTS, ports);
        if (expectsResponse) {
            Map<String, Object> response = portRow(
                    CommunicationCatalogContract.responsePortId(
                            exchangeSiteKey),
                    CommunicationCatalogContract.DIRECTION_RESPONSE,
                    "response", responseJavaType);
            response.put(
                    CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH,
                    CommunicationCatalogContract.RESPONSE_LEAF_PATH);
            row.put(CommunicationCatalogContract.RESPONSE_PORT, response);
            List<Map<String, Object>> components = new ArrayList<>();
            for (ResponseComponentPort component : responseComponents) {
                components.add(component.row(exchangeSiteKey));
            }
            if (!components.isEmpty()) {
                row.put(CommunicationCatalogContract.RESPONSE_COMPONENT_PORTS,
                        components);
            }
        }
        return row;
    }
}

/**
 * Recognises communication call sites inside an already target-selected
 * method.
 */
interface CommunicationCallSiteAdapter {
    /** Stable adapter name recorded on every row it produces. */
    String name();

    /** Classifies one invoke unit of a selected method, named by its
     *  enclosing method signature, Jimple unit index and declared callee. */
    CommunicationResolution resolve(String enclosingMethod, int unitIndex,
                                    String declaredCallee);

    /** Optional whole-slice pre-pass, run once before any {@link #resolve}. */
    default void prepare(Collection<String> selectedMethods) {
    }

    /** Selected methods this adapter recognises as transport implementation
     *  sites: frames that carry a remote call rather than decide one. */
    default Collection<String> transportImplementationMethods() {
        return Collections.emptySet();
    }
}

/** A recognised cut, a named gap, both, or nothing at all.  "Both" is the
 *  honest answer when the cut is certain but one of its ports is not. */
final class CommunicationResolution {
    private static final CommunicationResolution NONE =
            new CommunicationResolution(null, "", "", "");

    final CommunicationCallSite site;
    final String gapKind;
    final String gapReason;
    final String gapDetail;

    private CommunicationResolution(CommunicationCallSite site,
                                    String gapKind, String gapReason,
                                    String gapDetail) {
        this.site = site;
        this.gapKind = gapKind;
        this.gapReason = gapReason;
        this.gapDetail = gapDetail;
    }

    static CommunicationResolution none() {
        return NONE;
    }

    static CommunicationResolution site(CommunicationCallSite site) {
        return new CommunicationResolution(site, "", "", "");
    }

    static CommunicationResolution gap(String kind, String reason,
                                       String detail) {
        return new CommunicationResolution(null, kind, reason, detail);
    }

    static CommunicationResolution siteWithGap(CommunicationCallSite site,
                                               String kind, String reason,
                                               String detail) {
        return new CommunicationResolution(site, kind, reason, detail);
    }

    boolean isGap() {
        return !gapKind.isEmpty();
    }
}
