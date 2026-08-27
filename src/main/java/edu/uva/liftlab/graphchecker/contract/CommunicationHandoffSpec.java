package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * One site where this occurrence hands a declared communication port to the
 * VM, or takes one from it.  The VM is the single propagation authority: a
 * sender exports the live expression and a receiver attaches it, after which
 * the session ledger holds one {@code VALUE_HANDOFF} edge.  Nothing here pairs
 * anything: the port id, leaf path and direction are the port's own static
 * identity, never matched against a recorded export to recover a delivery.
 */
public final class CommunicationHandoffSpec {

    public static final String FIELD = "communicationHandoffs";
    /** This row kind's one name, in {@link #toString()}; never a wire
     *  member, because one kind per row is a constant, not a fact. */
    public static final String KIND = "COMMUNICATION_HANDOFF_SITE";
    /** This occurrence sends the port's value across the cut. */
    public static final String ROLE_EXPORT = "EXPORT";
    /** This occurrence receives the port's value from the cut. */
    public static final String ROLE_ATTACH = "ATTACH";
    public static final String ROLE = "role";

    private final String portId;
    private final String leafPath;
    private final String direction;
    private final String componentOfPortId;
    private final String encodingAuthority;
    private final String carrierClass;
    private final String carrierField;
    private final String carrierDescriptor;
    private final List<PathStep> handoffPath;
    private final String role;
    private final String method;
    private final String declaredCallee;
    private final int unitIndex;
    private final int argumentIndex;

    private CommunicationHandoffSpec(JsonObject encoded) {
        portId = string(encoded, CommunicationCatalogContract.PORT_ID);
        leafPath = string(encoded,
                CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH);
        direction = string(encoded,
                CommunicationCatalogContract.PORT_DIRECTION);
        componentOfPortId = string(encoded,
                CommunicationCatalogContract.PORT_COMPONENT_OF);
        encodingAuthority = string(encoded,
                CommunicationCatalogContract.PORT_ENCODING_AUTHORITY);
        carrierClass = string(encoded,
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_CLASS);
        carrierField = string(encoded,
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_FIELD);
        carrierDescriptor = string(encoded,
                CommunicationCatalogContract.PORT_MANUAL_CARRIER_DESCRIPTOR);
        handoffPath = decodePath(encoded);
        role = string(encoded, ROLE);
        String javaType = string(encoded,
                CommunicationCatalogContract.PORT_JAVA_TYPE);
        method = string(encoded,
                CommunicationCatalogContract.PORT_DEFINITION_METHOD);
        declaredCallee = string(encoded,
                CommunicationCatalogContract.DECLARED_CALLEE);
        unitIndex = integer(encoded,
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX, -1);
        argumentIndex = integer(encoded,
                CommunicationCatalogContract.PORT_ARGUMENT_INDEX, -1);
        boolean component = !componentOfPortId.isEmpty();
        boolean anyCarrier = !carrierClass.isEmpty() || !carrierField.isEmpty()
                || !carrierDescriptor.isEmpty();
        boolean manualCarrier = !carrierClass.isEmpty()
                && !carrierField.isEmpty() && !carrierDescriptor.isEmpty();
        boolean responsePathCarrier = !handoffPath.isEmpty();
        FieldPathSpec.DeclaredField pathLeaf = responsePathCarrier
                && handoffPath.get(handoffPath.size() - 1).field()
                ? FieldPathSpec.declaredField(handoffPath.get(
                handoffPath.size() - 1).declaration()) : null;
        if (portId.isEmpty() || leafPath.isEmpty() || direction.isEmpty()
                || javaType.isEmpty() || anyCarrier != manualCarrier
                || !manualCarrier && method.isEmpty()
                || component && (componentOfPortId.equals(portId)
                || encodingAuthority.isEmpty()
                || manualCarrier == responsePathCarrier)
                || !component && responsePathCarrier
                || responsePathCarrier
                && (!CommunicationCatalogContract.DIRECTION_RESPONSE.equals(
                direction) || pathLeaf == null
                || !javaType.equals(pathLeaf.type())
                || "void".equals(javaType))
                || (!ROLE_EXPORT.equals(role) && !ROLE_ATTACH.equals(role))) {
            throw new IllegalArgumentException(
                    "communication handoff site requires a declared port, "
                            + "leaf path, direction, type, exact site and role: "
                            + portId);
        }
    }

    private static List<PathStep> decodePath(JsonObject encoded) {
        JsonElement raw = encoded.get(
                CommunicationCatalogContract.PORT_HANDOFF_PATH);
        if (raw == null || raw.isJsonNull()) return Collections.emptyList();
        if (!raw.isJsonArray() || raw.getAsJsonArray().size() == 0) {
            throw new IllegalArgumentException(
                    "communication response handoff path must be non-empty");
        }
        List<PathStep> result = new ArrayList<>();
        for (JsonElement element : raw.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "communication response handoff step must be an object");
            }
            JsonObject step = element.getAsJsonObject();
            String kind = string(step, "kind");
            String declaration = string(step, "declaration");
            String elementType = string(step, "elementType");
            if (PathStep.FIELD.equals(kind)) {
                if (FieldPathSpec.declaredField(declaration) == null
                        || !elementType.isEmpty()) {
                    throw new IllegalArgumentException(
                            "response FIELD step requires one exact field");
                }
            } else if (PathStep.UNIQUE_ARRAY_ELEMENT.equals(kind)) {
                if (elementType.isEmpty() || !declaration.isEmpty()) {
                    throw new IllegalArgumentException(
                            "response UNIQUE_ARRAY_ELEMENT step requires "
                                    + "one elementType");
                }
            } else {
                throw new IllegalArgumentException(
                        "unsupported communication response path step: "
                                + kind);
            }
            result.add(new PathStep(kind, declaration, elementType));
        }
        if (!result.get(result.size() - 1).field()) {
            throw new IllegalArgumentException(
                    "communication response path must end at a field");
        }
        return Collections.unmodifiableList(result);
    }

    public static List<CommunicationHandoffSpec> decode(JsonObject task) {
        List<CommunicationHandoffSpec> sites = new ArrayList<>();
        if (task == null) return sites;
        JsonElement raw = task.get(FIELD);
        if (raw == null || !raw.isJsonArray()) return sites;
        for (JsonElement element : raw.getAsJsonArray()) {
            if (!element.isJsonObject()) {
                throw new IllegalArgumentException(
                        "communication handoff site must be an object");
            }
            sites.add(new CommunicationHandoffSpec(
                    element.getAsJsonObject()));
        }
        return Collections.unmodifiableList(sites);
    }

    public String portId() { return portId; }

    public String leafPath() { return leafPath; }

    public String direction() { return direction; }

    /** Structured carrier port this exact leaf crosses inside, or empty. */
    public String componentOfPortId() { return componentOfPortId; }

    /** True for an adapter-carried component, never a generic Java cut value. */
    public boolean component() { return !componentOfPortId.isEmpty(); }

    /** True when the adapter invokes the VM ABI on an exact carrier field. */
    public boolean manualCarrier() { return !carrierClass.isEmpty(); }

    /** True for a configured exact structural path rooted at an RPC response. */
    public boolean responsePathCarrier() { return !handoffPath.isEmpty(); }

    /** Canonical structural path; runtime never executes configured getters. */
    public List<PathStep> handoffPath() { return handoffPath; }

    public static final class PathStep {
        public static final String FIELD = "FIELD";
        public static final String UNIQUE_ARRAY_ELEMENT =
                "UNIQUE_ARRAY_ELEMENT";

        private final String kind;
        private final String declaration;
        private final String elementType;

        private PathStep(String kind, String declaration,
                         String elementType) {
            this.kind = kind;
            this.declaration = declaration;
            this.elementType = elementType;
        }

        public boolean field() { return FIELD.equals(kind); }

        public boolean uniqueArrayElement() {
            return UNIQUE_ARRAY_ELEMENT.equals(kind);
        }

        public String declaration() { return declaration; }

        public String elementType() { return elementType; }
    }

    public String carrierClass() { return carrierClass; }

    public String carrierField() { return carrierField; }

    public String carrierDescriptor() { return carrierDescriptor; }

    public String method() { return method; }

    /** Callee of the cut invoke, or {@code ""} at a server-entry site. */
    public String declaredCallee() { return declaredCallee; }

    public int unitIndex() { return unitIndex; }

    public int argumentIndex() { return argumentIndex; }

    public boolean exports() { return ROLE_EXPORT.equals(role); }

    public boolean exportsCutArgument() {
        return !manualCarrier() && exports() && unitIndex >= 0
                && argumentIndex >= 0
                && !declaredCallee.isEmpty();
    }

    public boolean exportsEntryReturn() {
        return !manualCarrier() && exports() && unitIndex < 0;
    }

    public boolean attachesEntryParameter() {
        return !manualCarrier() && !exports() && argumentIndex >= 0
                && unitIndex < 0;
    }

    public boolean attachesCutReturn() {
        return !manualCarrier() && !exports() && unitIndex >= 0
                && !declaredCallee.isEmpty();
    }

    /** {@code <method>#u<unitIndex>}, or the method for an entry site. */
    public String siteId() {
        if (manualCarrier()) {
            return carrierClass + "#" + carrierField + ":"
                    + carrierDescriptor;
        }
        return unitIndex < 0 ? method
                : CommunicationCatalogContract.siteId(method, unitIndex);
    }

    @Override
    public String toString() {
        return KIND + "[" + role + " " + portId + " " + leafPath + " @"
                + siteId() + "]";
    }
}
