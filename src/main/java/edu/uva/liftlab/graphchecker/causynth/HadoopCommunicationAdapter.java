package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import soot.SootMethod;
import soot.Type;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Hadoop-specific recognition of communication call sites, including the SASL
 * handshake README section 3 requires to move onto the same cut and handoff
 * abstraction rather than beside it.
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
    /** The handshake's own control plane, which lives in Hadoop's tree. */
    static final String SASL_CONTROL_PLANE_CLASS =
            "org.apache.hadoop.hdfs.protocol.datatransfer.sasl"
                    + ".CausynthSaslHandoff";
    /** The three leaves the encrypted handshake flattens into one name. */
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

    private final Map<String, SootMethod> methodsBySignature;
    private final ConfiguredProtocolStubs configured;
    /** The slice this run scans, kept so the transport half can be named. */
    private final Set<String> selectedMethods = new LinkedHashSet<>();
    /** Loaded entries by {@code class.name}, built once on first demand. */
    private Map<String, SootMethod> entriesByOwnerAndName;

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
    public void prepare(Collection<String> selected) {
        selectedMethods.clear();
        if (selected != null) {
            selectedMethods.addAll(selected);
        }
    }

    /** The selected frames Hadoop's own transport owns. */
    @Override
    public Collection<String> transportImplementationMethods() {
        Set<String> transport = new LinkedHashSet<>();
        for (String method : selectedMethods) {
            String owner = CausynthStaticFacts.methodOwner(method);
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
        String owner = CausynthStaticFacts.methodOwner(declaredCallee);
        String name = CausynthStaticFacts.methodName(declaredCallee);
        if (owner.isEmpty()) {
            return CommunicationResolution.none();
        }
        // A transport frame is an implementation site.
        if (transportImplementationClass(
                CausynthStaticFacts.methodOwner(enclosingMethod))) {
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
        // endpoints.
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

    private CommunicationResolution resolveSasl(String enclosingMethod,
                                                int unitIndex,
                                                String declaredCallee) {
        SootMethod client = methodsBySignature.get(declaredCallee);
        if (client == null) {
            return CommunicationResolution.gap(
                    CommunicationCatalogContract.GAP_CALL_SITE_UNRESOLVED,
                    "SASL_CLIENT_METHOD_NOT_LOADED", declaredCallee);
        }
        SootMethod server = uniqueEntry(SASL_SERVER_CLASS,
                SASL_SERVER_METHOD);
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

    /** Declares the three handshake leaves as component ports of the encoded
     *  SASL user name (README section 3), and returns the components no
     *  declared string port could host, if any. */
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

    /** The one loaded {@code class.name} entry, or null when the catalog
     *  holds none or more than one. */
    private SootMethod uniqueEntry(String owner, String name) {
        if (entriesByOwnerAndName == null) {
            entriesByOwnerAndName = new LinkedHashMap<>();
            for (SootMethod candidate : methodsBySignature.values()) {
                String key = candidate.getDeclaringClass().getName() + "."
                        + candidate.getName();
                entriesByOwnerAndName.put(key,
                        entriesByOwnerAndName.containsKey(key)
                                ? null : candidate);
            }
        }
        return entriesByOwnerAndName.get(owner + "." + name);
    }

    /** True only at the encrypted-key caller of the shared SASL helper. */
    private static boolean encryptedSaslCaller(String enclosingMethod) {
        return SASL_CLIENT_CLASS.equals(
                CausynthStaticFacts.methodOwner(enclosingMethod))
                && SASL_ENCRYPTED_CALLER_METHOD.equals(
                CausynthStaticFacts.methodName(enclosingMethod));
    }

    /** True for the frames that carry a remote call rather than decide it. */
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

}
