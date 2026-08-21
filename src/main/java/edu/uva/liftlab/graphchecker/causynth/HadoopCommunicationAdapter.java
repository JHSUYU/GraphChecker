package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import soot.Body;
import soot.SootMethod;
import soot.Type;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Hadoop-specific recognition of communication call sites.
 *
 * <p>All Hadoop knowledge in the Step 1 static half lives here.  The
 * catalog algorithm consumes only {@link CommunicationCallSite}, so a
 * different transport can be supported by adding an adapter and touching no
 * CFG code.</p>
 *
 * <p>The configured protocol catalog is the admission authority.  The
 * adapter resolves an endpoint, and the SASL component leaves when needed,
 * only after the declared callee appears in that catalog.  Loading Hadoop
 * therefore never turns every protocol-like method in the process into a
 * communication boundary.</p>
 *
 * <h2>Where the cuts are</h2>
 *
 * <p>The client cut is the outer application call on the protocol interface
 * ({@code NamenodeProtocol.getBlockKeys}, {@code DatanodeProtocol
 * .sendHeartbeat}).  The server cut is the post-deserialization semantic
 * entry: the unique non-transport application implementation of the same
 * sub-signature ({@code NameNodeRpcServer}).  Translator, ProtoBuf and
 * transport frames ({@code *TranslatorPB}, {@code *ProtocolPB},
 * {@code org.apache.hadoop.ipc.*}, dynamic proxies) are implementation
 * sites: they neither open a cut nor receive one, so one Hadoop RPC yields
 * exactly one client cut and one server cut.</p>
 *
 * <h2>SASL</h2>
 *
 * <p>The encrypted HDFS data-transfer handshake is a single named pair rather
 * than an annotated protocol: {@code getEncryptedStreams} calls
 * {@code SaslDataTransferClient.doSaslHandshake}, and the server semantic
 * entry is {@code SaslDataTransferServer.getEncryptionKeyFromUserName}, the
 * site that parses the key id, block-pool id and nonce and delegates the
 * lookup.  The ordinary token-based {@code getSaslStreams} branch calls the
 * same helper but has a different server credential path, so it is not this
 * pair.  Request correspondence is derived by unique erased-type match
 * against the server parameters; an ambiguous or missing match is a named
 * gap, never a positional guess.</p>
 *
 * <p>That match yields one port, because the handshake carries one argument:
 * the encoded SASL user name.  The three values that actually cross - the key
 * id, the block-pool id and the nonce - are components of that one string, so
 * they are declared as component ports of it.  Without them the cut would
 * declare a name and the runtime handoff would transport three leaves that no
 * region catalog knows, which is README section 3's requirement that SASL move
 * onto the same cut and handoff abstraction rather than beside it.</p>
 */
final class HadoopCommunicationAdapter implements
        CommunicationCallSiteAdapter {
    static final String NAME = "HADOOP";

    static final String SASL_CLIENT_CLASS =
            "org.apache.hadoop.hdfs.protocol.datatransfer.sasl"
                    + ".SaslDataTransferClient";
    static final String SASL_CLIENT_METHOD = "doSaslHandshake";
    private static final String SASL_ENCRYPTED_CALLER_METHOD =
            "getEncryptedStreams";
    static final String SASL_SERVER_CLASS =
            "org.apache.hadoop.hdfs.protocol.datatransfer.sasl"
                    + ".SaslDataTransferServer";
    static final String SASL_SERVER_METHOD =
            "getEncryptionKeyFromUserName";
    static final String SASL_PROTOCOL = "HDFS_DATA_TRANSFER_SASL";
    /**
     * The handshake's own control plane, which lives in Hadoop's tree.
     *
     * <p>It allocates the exchange, declares the handshake's {@code SEND} and
     * {@code RECEIVE} legs and carries the three encoded leaves across them.
     * That is transport work by the same rule {@code org.apache.hadoop.ipc.*}
     * is transport work; it just happens to sit in a package prefix no
     * structural rule names.  Left undeclared it reads as ordinary state of
     * whichever region holds the handshake, which is a different claim from
     * the true one.</p>
     */
    static final String SASL_CONTROL_PLANE_CLASS =
            "org.apache.hadoop.hdfs.protocol.datatransfer.sasl"
                    + ".CausynthSaslHandoff";
    /**
     * The three leaves the encrypted handshake flattens into one user name.
     *
     * <p>These are the component names of the encoded name, and they are also
     * what the server entry calls its own parsed values.  The runtime adapter
     * states the same leaf names, so one declared port and one transported
     * leaf are the same port.</p>
     */
    static final String[] SASL_LEAF_NAMES =
            {"keyId", "blockPoolId", "nonce"};
    static final String[] SASL_LEAF_TYPES =
            {"int", "java.lang.String", "byte[]"};
    static final String[] SASL_LEAF_DESCRIPTORS =
            {"I", "Ljava/lang/String;", "[B"};
    static final String SASL_EXPORT_CARRIER_CLASS =
            "org.apache.hadoop.hdfs.security.token.block.DataEncryptionKey";
    static final String SASL_ATTACH_CARRIER_CLASS =
            SASL_CONTROL_PLANE_CLASS + "$Parsed";
    /** Who states that the user name encodes exactly those three leaves. */
    static final String SASL_ENCODING_AUTHORITY =
            "HDFS_DATA_TRANSFER_SASL_NAME_ENCODING_V1";
    /** Namespace the SASL handshake's broker leaf paths are stated under. */
    static final String SASL_HANDOFF_LEAF_PREFIX = "HANDSHAKE/";

    private static final Pattern SIGNATURE = Pattern.compile(
            "<([^:]+):\\s+(\\S+)\\s+([^\\s(]+)\\((.*)\\)>");

    private final Map<String, SootMethod> methodsBySignature;
    private final ConfiguredProtocolStubs configured;
    /** The slice this run scans, kept so the transport half can be named. */
    private final Set<String> selectedMethods = new LinkedHashSet<>();

    HadoopCommunicationAdapter(Map<String, SootMethod> methodsBySignature,
                               ConfiguredProtocolStubs configured) {
        if (methodsBySignature == null) {
            throw new IllegalArgumentException(
                    "loaded method catalog is required");
        }
        if (configured == null) {
            throw new IllegalArgumentException(
                    "configured protocol catalog is required");
        }
        this.methodsBySignature = methodsBySignature;
        this.configured = configured;
    }

    @Override
    public String name() {
        return NAME;
    }

    @Override
    public void prepare(Collection<String> selected,
                        Function<String, Body> bodies) {
        selectedMethods.clear();
        if (selected != null) {
            selectedMethods.addAll(selected);
        }
    }

    /**
     * The selected frames Hadoop's own transport owns.
     *
     * <p>{@link #transportImplementationClass} is already the rule this
     * adapter applies to keep one remote call to one cut; it refuses to open a
     * cut inside such a frame and refuses to let one stand in for the semantic
     * server entry.  The same rule read forward names the frames themselves,
     * which is what a consumer needs in order to tell a frame on the far side
     * of a cut from a frame nothing has attributed yet.</p>
     *
     * <p>{@link #SASL_CLIENT_CLASS} is added because the HDFS data-transfer
     * handshake is a named pair rather than an annotated protocol: the class
     * carries the handshake and matches no naming rule above.  Its server
     * counterpart is deliberately absent - {@link #SASL_SERVER_METHOD} is a
     * semantic server entry, not transport - and the planner subtracts every
     * resolved entry from this set in any case.</p>
     */
    @Override
    public Collection<String> transportImplementationMethods() {
        Set<String> transport = new LinkedHashSet<>();
        for (String method : selectedMethods) {
            String owner = declaringClassOf(method);
            if (transportImplementationClass(owner)
                    || SASL_CLIENT_CLASS.equals(owner)
                    || saslControlPlaneClass(owner)) {
                transport.add(method);
            }
        }
        return transport;
    }

    @Override
    public CommunicationResolution resolve(String enclosingMethod,
                                           int unitIndex,
                                           String declaredCallee) {
        if (declaredCallee == null || declaredCallee.isEmpty()) {
            return CommunicationResolution.none();
        }
        List<ProtocolStubMapping> admitted = configured.targets(
                declaredCallee);
        if (admitted.isEmpty()) {
            return CommunicationResolution.none();
        }
        Matcher matcher = SIGNATURE.matcher(declaredCallee);
        if (!matcher.matches()) {
            return CommunicationResolution.none();
        }
        String owner = matcher.group(1);
        String name = matcher.group(3);
        // A transport frame is an implementation site.  Recognising a cut
        // inside one would split the same remote call twice.
        if (transportImplementationClass(
                declaringClassOf(enclosingMethod))) {
            return CommunicationResolution.none();
        }
        if (SASL_CLIENT_CLASS.equals(owner)
                && SASL_CLIENT_METHOD.equals(name)) {
            if (!encryptedSaslCaller(enclosingMethod)) {
                return CommunicationResolution.none();
            }
            return resolveSasl(enclosingMethod, unitIndex, declaredCallee);
        }
        // In production the explicit catalog has already named both semantic
        // endpoints.  Do not run that fact back through protocol-interface
        // discovery: Hadoop application code often calls a concrete PB
        // translator (for example BPServiceActor's heartbeat), whose class is
        // intentionally not itself annotated as a protocol interface.  The
        // old second gate admitted the row and then silently discarded the
        // real call site, leaving only unrelated test helpers that happened
        // to invoke the interface type directly.
        if (admitted.size() != 1) {
            return CommunicationResolution.gap(
                    CommunicationCatalogContract.GAP_CALL_SITE_UNRESOLVED,
                    "AMBIGUOUS_CONFIGURED_ENDPOINTS",
                    declaredCallee + " -> " + admitted.size());
        }
        return resolveConfigured(enclosingMethod, unitIndex,
                declaredCallee, admitted.get(0));
    }

    /** Lowers one catalog row into a typed static cut. */
    private CommunicationResolution resolveConfigured(
            String enclosingMethod, int unitIndex, String declaredCallee,
            ProtocolStubMapping mapping) {
        SootMethod client = methodsBySignature.get(mapping.clientStub);
        SootMethod server = methodsBySignature.get(mapping.serverStub);
        if (client == null || server == null || !server.isConcrete()) {
            return CommunicationResolution.gap(
                    CommunicationCatalogContract.GAP_CALL_SITE_UNRESOLVED,
                    "CONFIGURED_ENDPOINT_NOT_LOADED",
                    mapping.clientStub + " -> " + mapping.serverStub);
        }
        List<CommunicationCallSite.RequestPort> request = new ArrayList<>();
        for (ProtocolPortMapping port : mapping.request) {
            request.add(new CommunicationCallSite.RequestPort(port.name,
                    port.clientArgument, port.serverParameter,
                    client.getParameterType(port.clientArgument).toString()));
        }
        String responseType = mapping.response
                ? client.getReturnType().toString() : "";
        List<CommunicationCallSite.ResponseComponentPort>
                responseComponents = new ArrayList<>();
        for (ResponseComponentMapping component
                : mapping.responseComponents) {
            responseComponents.add(
                    new CommunicationCallSite.ResponseComponentPort(
                            component.name, component.javaType,
                            component.path));
        }
        return CommunicationResolution.site(new CommunicationCallSite(
                enclosingMethod, unitIndex, NAME, mapping.transport,
                mapping.id, declaredCallee,
                Collections.singletonList(mapping.serverStub),
                mapping.response, responseType, request,
                responseComponents));
    }

    // ------------------------------------------------------------------
    // HDFS data-transfer SASL
    // ------------------------------------------------------------------

    private CommunicationResolution resolveSasl(String enclosingMethod,
                                                int unitIndex,
                                                String declaredCallee) {
        SootMethod client = methodsBySignature.get(declaredCallee);
        if (client == null) {
            return CommunicationResolution.gap(
                    CommunicationCatalogContract.GAP_CALL_SITE_UNRESOLVED,
                    "SASL_CLIENT_METHOD_NOT_LOADED", declaredCallee);
        }
        SootMethod server = saslServerEntry();
        if (server == null) {
            return CommunicationResolution.gap(
                    CommunicationCatalogContract.GAP_SERVER_CUT_UNRESOLVED,
                    "SASL_SERVER_ENTRY_MISSING",
                    SASL_SERVER_CLASS + "." + SASL_SERVER_METHOD);
        }
        List<CommunicationCallSite.RequestPort> request = new ArrayList<>();
        List<String> unresolved = new ArrayList<>();
        for (int index = 0; index < server.getParameterCount(); index++) {
            Type wanted = server.getParameterType(index);
            List<Integer> matches = new ArrayList<>();
            for (int arg = 0; arg < client.getParameterCount(); arg++) {
                if (client.getParameterType(arg).equals(wanted)) {
                    matches.add(arg);
                }
            }
            if (matches.size() == 1) {
                request.add(new CommunicationCallSite.RequestPort(
                        "p" + index, matches.get(0), index,
                        wanted.toString()));
            } else {
                unresolved.add(index + ":" + wanted);
            }
        }
        List<String> undeclared = saslComponentPorts(request);
        CommunicationCallSite site = new CommunicationCallSite(
                enclosingMethod, unitIndex, NAME,
                CommunicationCatalogContract.TRANSPORT_SASL_HANDSHAKE,
                SASL_PROTOCOL, declaredCallee,
                Collections.singletonList(server.getSignature()),
                false, "", request, Collections
                .<CommunicationCallSite.ResponseComponentPort>emptyList());
        if (!unresolved.isEmpty()) {
            // The root cause when both fire: no unique type match is also why
            // no string port could host the three handshake components.
            return CommunicationResolution.siteWithGap(site,
                    CommunicationCatalogContract.GAP_REQUEST_PORT_UNRESOLVED,
                    "NO_UNIQUE_TYPE_MATCH", String.join(",", unresolved));
        }
        if (!undeclared.isEmpty()) {
            return CommunicationResolution.siteWithGap(site,
                    CommunicationCatalogContract.GAP_REQUEST_PORT_UNRESOLVED,
                    "SASL_ENCODED_NAME_PORT_ABSENT",
                    String.join(",", undeclared));
        }
        return CommunicationResolution.site(site);
    }

    /**
     * Declares the three handshake leaves as component ports of the encoded
     * SASL user name.
     *
     * <p>README section 3: "The existing SASL adapter exposes selected
     * {@code keyId}, {@code blockPoolId} and nonce leaves across their
     * concrete encoding.  Step 1 must move it onto the same cut and handoff
     * abstraction."  The cut itself carries a single {@code String} argument -
     * the client flattens the key into one name and the server splits, parses
     * and Base64-decodes it back out - so without this the three leaves the
     * runtime adapter really transports have no declared port to be equal
     * over, and every SASL handoff equality is stated about a name no region
     * catalog knows.</p>
     *
     * <p>The encoding is a real value transformation, not a serialization
     * detail, so nothing here claims to execute it: the ports state which
     * leaves cross and what type each has, and the runtime handoff states the
     * expression each one carried.  Their names are the components the
     * handshake defines, which is also what the server entry's own parameters
     * are called, so the runtime adapter can name the very same leaf.</p>
     *
     * @return the components no declared string port could host, if any
     */
    private static List<String> saslComponentPorts(
            List<CommunicationCallSite.RequestPort> request) {
        String encoded = "";
        for (CommunicationCallSite.RequestPort port : request) {
            if ("java.lang.String".equals(port.javaType)) {
                if (!encoded.isEmpty()) {
                    // Two string arguments and no way to say which one is the
                    // encoded name: naming one would be a positional guess.
                    return Arrays.asList(SASL_LEAF_NAMES);
                }
                encoded = port.name;
            }
        }
        if (encoded.isEmpty()) {
            return Arrays.asList(SASL_LEAF_NAMES);
        }
        for (int index = 0; index < SASL_LEAF_NAMES.length; index++) {
            request.add(new CommunicationCallSite.RequestPort(
                    SASL_LEAF_NAMES[index], -1, -1, SASL_LEAF_TYPES[index],
                    encoded, SASL_ENCODING_AUTHORITY,
                    SASL_HANDOFF_LEAF_PREFIX + SASL_LEAF_NAMES[index],
                    SASL_EXPORT_CARRIER_CLASS, SASL_LEAF_NAMES[index],
                    SASL_LEAF_DESCRIPTORS[index],
                    SASL_ATTACH_CARRIER_CLASS, SASL_LEAF_NAMES[index],
                    SASL_LEAF_DESCRIPTORS[index]));
        }
        return Collections.emptyList();
    }

    private SootMethod saslServerEntry() {
        SootMethod resolved = null;
        for (SootMethod candidate : methodsBySignature.values()) {
            if (!SASL_SERVER_METHOD.equals(candidate.getName())
                    || !SASL_SERVER_CLASS.equals(
                    candidate.getDeclaringClass().getName())) {
                continue;
            }
            if (resolved != null) {
                return null;
            }
            resolved = candidate;
        }
        return resolved;
    }

    /** True only at the encrypted-key caller of the shared SASL helper. */
    private static boolean encryptedSaslCaller(String enclosingMethod) {
        if (enclosingMethod == null) {
            return false;
        }
        Matcher matcher = SIGNATURE.matcher(enclosingMethod);
        return matcher.matches()
                && SASL_CLIENT_CLASS.equals(matcher.group(1))
                && SASL_ENCRYPTED_CALLER_METHOD.equals(matcher.group(3));
    }

    // ------------------------------------------------------------------
    // Structural indices
    // ------------------------------------------------------------------

    /**
     * True for the frames that carry a remote call rather than decide it.
     * These are implementation sites: they never open or receive a cut.
     */
    static boolean transportImplementationClass(String className) {
        if (className == null || className.isEmpty()) {
            return false;
        }
        return className.startsWith("org.apache.hadoop.ipc.")
                || className.contains("TranslatorPB")
                || className.endsWith("ProtocolPB")
                || className.contains(".protocolPB.")
                || className.contains("$Proxy")
                || className.startsWith("com.sun.proxy.");
    }

    /** True for the handshake control plane and its carrier types. */
    private static boolean saslControlPlaneClass(String className) {
        return className != null
                && (SASL_CONTROL_PLANE_CLASS.equals(className)
                || className.startsWith(SASL_CONTROL_PLANE_CLASS + "$"));
    }

    private static String declaringClassOf(String methodSignature) {
        if (methodSignature == null) {
            return "";
        }
        Matcher matcher = SIGNATURE.matcher(methodSignature);
        return matcher.matches() ? matcher.group(1) : "";
    }

}
