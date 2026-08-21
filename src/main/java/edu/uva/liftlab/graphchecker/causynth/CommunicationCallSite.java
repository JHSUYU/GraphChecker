package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import soot.Body;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * One transport-neutral description of a selected communication call site.
 *
 * <p>The generic catalog code in {@link CommunicationCatalogPlanner}
 * consumes only this description.  It never asks what Hadoop is, which
 * protocol interface was matched or how a server entry was found: a
 * {@link CommunicationCallSiteAdapter} answers that and hands back this
 * record, so protocol knowledge stays out of the discovery algorithm.</p>
 *
 * <p>Both the client cut and the server entry are semantic sites.  One
 * remote call produces exactly one client cut and exactly one server cut;
 * transport, serialization and translator frames between them are
 * implementation sites and never become call sites of their own.</p>
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
     * Every semantic server entry this cut may reach.
     *
     * <p>Usually one.  Several means the slice holds more than one
     * compatible entry and static analysis cannot say which of them this cut
     * delivers to: README section 1 is explicit that "call order, or a static
     * endpoint match never prove an RPC edge", and README Step 4 deletes
     * FIFO/span pairing outright, so discovery keeps all of them as
     * candidates instead of ordering them into a guess.  The planner
     * catalogs every candidate and the accompanying gap row names the set;
     * only the runtime attempt identity resolves it.</p>
     *
     * <p>The list <em>is</em> a row field, and the distinction it rests on is
     * worth stating: {@link #serverEntryMethod} is an answer and this is a
     * bound.  Discovery really did establish "these entries and no others",
     * so publishing the set states something it proved, while publishing one
     * of its members would state something it did not.  The runtime needs the
     * bound because it holds evidence discovery does not - the recorded
     * {@code SEND} invocation identifies the cut exactly, and the serving
     * activation recorded its own {@code RECEIVE} - and those two recorded
     * facts pair a delivery with a fragment.  This list only decides which
     * pairings are admissible; a fragment it does not name is refused.  The
     * accompanying {@link CommunicationCatalogContract#GAP_SERVER_CUT_UNRESOLVED}
     * row stays either way, because an admissible set larger than one is
     * still an unresolved static pairing.</p>
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
        this.responseJavaType = responseJavaType == null
                ? "" : responseJavaType;
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
            Map<String, Object> port = new LinkedHashMap<>();
            port.put(CommunicationCatalogContract.PORT_ID,
                    CommunicationCatalogContract.responseComponentPortId(
                            exchangeSiteKey, name));
            port.put(CommunicationCatalogContract.PORT_DIRECTION,
                    CommunicationCatalogContract.DIRECTION_RESPONSE);
            port.put(CommunicationCatalogContract.PORT_NAME, name);
            port.put(CommunicationCatalogContract.PORT_JAVA_TYPE, javaType);
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
        /**
         * Name of the request port this one is a component of, or {@code ""}.
         *
         * <p>A component port is a leaf that crosses the cut <em>inside</em>
         * another port's value rather than as an argument of its own.  The
         * HDFS data-transfer handshake is the case README section 3 names:
         * the client flattens {@code keyId}, {@code blockPoolId} and
         * {@code nonce} into one SASL user name and the server parses them
         * back out, so the cut carries one string argument and three declared
         * leaves.  The encoding is a real value transformation, so the model
         * does not execute it symbolically; the handoff states it, and the
         * component ports are where that statement lands.</p>
         */
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
                    String handoffLeafPath) {
            this(name, clientArgumentIndex, serverParameterIndex, javaType,
                    componentOf, encodingAuthority, handoffLeafPath,
                    "", "", "", "", "", "");
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
            this.componentOf = componentOf == null ? "" : componentOf;
            this.encodingAuthority = encodingAuthority == null
                    ? "" : encodingAuthority;
            this.handoffLeafPath = handoffLeafPath == null
                    ? "" : handoffLeafPath;
            this.exportCarrierClass = exportCarrierClass == null
                    ? "" : exportCarrierClass;
            this.exportCarrierField = exportCarrierField == null
                    ? "" : exportCarrierField;
            this.exportCarrierDescriptor = exportCarrierDescriptor == null
                    ? "" : exportCarrierDescriptor;
            this.attachCarrierClass = attachCarrierClass == null
                    ? "" : attachCarrierClass;
            this.attachCarrierField = attachCarrierField == null
                    ? "" : attachCarrierField;
            this.attachCarrierDescriptor = attachCarrierDescriptor == null
                    ? "" : attachCarrierDescriptor;
        }

        Map<String, Object> row(String exchangeSiteKey) {
            Map<String, Object> port = new LinkedHashMap<>();
            port.put(CommunicationCatalogContract.PORT_ID,
                    CommunicationCatalogContract.requestPortId(
                            exchangeSiteKey, name));
            port.put(CommunicationCatalogContract.PORT_DIRECTION,
                    CommunicationCatalogContract.DIRECTION_REQUEST);
            port.put(CommunicationCatalogContract.PORT_NAME, name);
            port.put(CommunicationCatalogContract.PORT_JAVA_TYPE, javaType);
            port.put(CommunicationCatalogContract.PORT_CLIENT_ARGUMENT_INDEX, clientArgumentIndex);
            port.put(CommunicationCatalogContract.PORT_SERVER_PARAMETER_INDEX, serverParameterIndex);
            if (!componentOf.isEmpty()) {
                port.put(CommunicationCatalogContract.PORT_COMPONENT_OF,
                        CommunicationCatalogContract.requestPortId(
                                exchangeSiteKey, componentOf));
                port.put(CommunicationCatalogContract.PORT_ENCODING_AUTHORITY, encodingAuthority);
            }
            // Every declared port names the leaf the broker addresses it by,
            // on both sides of the cut.  A wire adapter that namespaces its
            // leaves states one; an ordinary port carries one value, so the
            // port *is* the leaf and its own name is that address.  Without
            // this the receiving declaration had no leaf to land an attach
            // on, and only the SASL components ever had one.
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
        Map<String, Object> row = new LinkedHashMap<>();
        row.put(CommunicationCatalogContract.SCHEMA_VERSION_FIELD,
                CommunicationCatalogContract.SCHEMA_VERSION);
        row.put(CommunicationCatalogContract.KIND,
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
            Map<String, Object> response = new LinkedHashMap<>();
            response.put(CommunicationCatalogContract.PORT_ID,
                    CommunicationCatalogContract.responsePortId(
                            exchangeSiteKey));
            response.put(CommunicationCatalogContract.PORT_DIRECTION,
                    CommunicationCatalogContract.DIRECTION_RESPONSE);
            response.put(CommunicationCatalogContract.PORT_NAME, "response");
            response.put(CommunicationCatalogContract.PORT_JAVA_TYPE,
                    responseJavaType);
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
 * method.  An adapter is the only place protocol-specific knowledge lives.
 *
 * <p>An adapter must never guess.  When a site looks like communication but
 * cannot be resolved, it returns {@link CommunicationResolution#gap} so the
 * gap is named instead of an edge being invented.</p>
 */
interface CommunicationCallSiteAdapter {
    /** Stable adapter name recorded on every row it produces. */
    String name();

    /**
     * Classifies one invoke unit of a selected method.
     *
     * @param enclosingMethod signature of the method holding the unit
     * @param unitIndex       Jimple unit index of the invoke
     * @param declaredCallee  callee signature declared at the call site
     */
    CommunicationResolution resolve(String enclosingMethod, int unitIndex,
                                    String declaredCallee);

    /**
     * Optional whole-slice pre-pass, run once before any {@link #resolve}.
     *
     * <p>An adapter whose server side is found by structure rather than by
     * type needs to see the slice before it can answer about a single call
     * site.  An adapter that resolves a site from the site alone ignores
     * this.</p>
     */
    default void prepare(Collection<String> selectedMethods,
                         Function<String, Body> bodies) {
    }

    /**
     * Communication the slice declares that discovery produced no cut for,
     * asked once after every {@link #resolve}.
     *
     * <p>Zero call sites also means zero call-site gaps, so without this hook
     * an adapter that recognises nothing in a communicating slice is
     * indistinguishable from a slice that does not communicate.  An adapter
     * that can tell the difference reports it here.</p>
     */
    default List<CommunicationDeclarationGap> uncutDeclarations() {
        return Collections.emptyList();
    }

    /**
     * Selected methods this adapter recognises as transport implementation
     * sites: frames that carry a remote call rather than decide one.
     *
     * <p>An adapter already has to know these to keep one exchange to one
     * cut - it refuses to open a cut inside one of them - so this hook only
     * publishes an answer it has already computed.  The planner adds the cut
     * callees itself, so an adapter that has nothing further to say may leave
     * this empty; what it is for is the <em>receiving</em> half, which no cut
     * names.</p>
     *
     * <p>A method the same slice resolves as a client cut holder or as a
     * semantic server entry is a decision site, and the planner drops it from
     * this set rather than letting a declaration silence a fragment.</p>
     *
     * <p>Asked once, after {@link #prepare} and every {@link #resolve}.</p>
     */
    default Collection<String> transportImplementationMethods() {
        return Collections.emptySet();
    }
}

/**
 * One declared exchange the slice exercises that produced no cut.
 *
 * <p>Carries only what a gap row needs; the adapter names the gap and the
 * planner writes the row, so gap formatting stays in one place.</p>
 */
final class CommunicationDeclarationGap {
    final String kind;
    final String reason;
    final String method;
    final String siteId;
    final String detail;

    CommunicationDeclarationGap(String kind, String reason, String method,
                                String siteId, String detail) {
        this.kind = kind;
        this.reason = reason;
        this.method = method;
        this.siteId = siteId;
        this.detail = detail;
    }
}

/**
 * A recognised cut, a named gap, both, or nothing at all.
 *
 * <p>"Both" is the honest answer when the cut itself is certain but one of
 * its ports is not: the call site still exists and the unresolved port is
 * named rather than positionally guessed.</p>
 */
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
