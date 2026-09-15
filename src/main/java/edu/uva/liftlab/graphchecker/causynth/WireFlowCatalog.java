package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.d3.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.d3.plan.SiteId;
import soot.Body;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.jimple.Stmt;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.causynth.ConcolicInstrumentationSelections.firstNonBlank;

/** Strict, transport-neutral declarations of values carried by messages. */
final class WireFlowCatalog {
    static final String PROPERTY = "causynth.communication.mappings";
    static final String ENVIRONMENT = "CAUSYNTH_COMMUNICATION_MAPPINGS";
    static final String KIND = "WIRE_FLOW";
    static final int SCHEMA_VERSION = 1;
    static final String PRODUCER = "producer";
    static final String CONSUMER = "consumer";

    private final List<WireFlow> flows;

    private WireFlowCatalog(List<WireFlow> flows) {
        this.flows = Collections.unmodifiableList(new ArrayList<>(flows));
    }

    static WireFlowCatalog fromConfiguration(
            Map<String, SootMethod> methods) throws IOException {
        String configured = firstNonBlank(System.getProperty(PROPERTY),
                System.getenv(ENVIRONMENT));
        if (configured == null) return new WireFlowCatalog(
                Collections.<WireFlow>emptyList());
        Path path = Paths.get(configured).toAbsolutePath().normalize();
        if (!Files.isRegularFile(path)) {
            throw new IOException("Communication mapping not found: " + path);
        }
        List<WireFlow> flows = new ArrayList<>();
        try (BufferedReader reader = Files.newBufferedReader(path,
                StandardCharsets.UTF_8)) {
            String line;
            int lineNumber = 0;
            while ((line = reader.readLine()) != null) {
                lineNumber++;
                if (line.trim().isEmpty()) continue;
                try {
                    JsonElement parsed = JsonParser.parseString(line);
                    if (!parsed.isJsonObject()) {
                        throw new IllegalArgumentException(
                                "mapping must be an object");
                    }
                    flows.add(parse(parsed.getAsJsonObject(), methods));
                } catch (RuntimeException invalid) {
                    throw new IOException("Invalid communication mapping at "
                            + path + ":" + lineNumber + ": "
                            + invalid.getMessage(), invalid);
                }
            }
        }
        return new WireFlowCatalog(flows);
    }

    List<WireFlow> flows() {
        return flows;
    }

    private static WireFlow parse(JsonObject row,
                                  Map<String, SootMethod> methods) {
        if (integer(row, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(string(row, "kind"))) {
            // Named with the record, never skipped: a declared flow this
            // build cannot read is a port that will not mint, and a silent
            // skip turns that into "the workload never sent it".
            throw new IllegalArgumentException(
                    "communication mapping " + string(row, "id")
                            + " states schemaVersion "
                            + integer(row, "schemaVersion", -1) + " kind "
                            + string(row, "kind") + "; this build reads"
                            + " schemaVersion " + SCHEMA_VERSION + " kind "
                            + KIND);
        }
        String id = string(row, "id");
        String transport = string(row, "transport");
        String direction = string(row, "direction").toUpperCase();
        String javaType = string(row, "javaType");
        if (id.isEmpty() || transport.isEmpty() || javaType.isEmpty()
                || !(CommunicationCatalogContract.DIRECTION_REQUEST.equals(
                direction) || CommunicationCatalogContract.DIRECTION_RESPONSE
                .equals(direction))) {
            throw new IllegalArgumentException(
                    "wire flow requires id, transport, REQUEST/RESPONSE and javaType");
        }
        CaptureSite producer = CaptureSite.parse(object(row, PRODUCER),
                methods, frameMethod(row, "producerFrameMethod", methods));
        CaptureSite consumer = CaptureSite.parse(object(row, CONSUMER),
                methods, frameMethod(row, "consumerFrameMethod", methods));
        if (!javaType.equals(producer.javaType)
                || !javaType.equals(consumer.javaType)) {
            throw new IllegalArgumentException("wire endpoint types differ for "
                    + id + ": " + producer.javaType + " -> "
                    + consumer.javaType + " (declared " + javaType + ")");
        }
        return new WireFlow(id, transport, direction, javaType,
                producer, consumer);
    }

    /**
     * One side's declared frame method, or "".
     *
     * <p>A port is one pair of bytecode sites and a protocol sends many
     * unrelated values of that shape through it.  The frame method is the one
     * whose single call builds one instance of the value the port belongs to,
     * so the leaves of that instance are addressed within it and two groups of
     * the same shape in one message stay apart.  Declaring none is allowed and
     * means the RPC message itself is the frame.</p>
     */
    private static String frameMethod(JsonObject row, String name,
                                      Map<String, SootMethod> methods) {
        String declared = string(row, name);
        if (declared.isEmpty()) return "";
        SootMethod method = methods.get(declared);
        if (method == null || !method.isConcrete()) {
            throw new IllegalArgumentException(
                    "frame method did not resolve: " + declared);
        }
        return declared;
    }

    private static JsonObject object(JsonObject row, String name) {
        JsonElement value = row.get(name);
        if (value == null || !value.isJsonObject()) {
            throw new IllegalArgumentException(name + " capture is required");
        }
        return value.getAsJsonObject();
    }

    private static String string(JsonObject row, String name) {
        JsonElement value = row.get(name);
        return value == null || value.isJsonNull()
                ? "" : value.getAsString().trim();
    }

    private static int integer(JsonObject row, String name, int fallback) {
        JsonElement value = row.get(name);
        return value == null || value.isJsonNull()
                ? fallback : value.getAsInt();
    }

    static final class WireFlow {
        final String id;
        final String transport;
        final String direction;
        final String javaType;
        final CaptureSite producer;
        final CaptureSite consumer;
        final String exchangeSiteKey;
        final String portId;

        private WireFlow(String id, String transport, String direction,
                         String javaType, CaptureSite producer,
                         CaptureSite consumer) {
            this.id = id;
            this.transport = transport;
            this.direction = direction;
            this.javaType = javaType;
            this.producer = producer;
            this.consumer = consumer;
            exchangeSiteKey = CommunicationCatalogContract.exchangeSiteKey(
                    transport, id, client().siteId(), client().callee,
                    server().method);
            portId = CommunicationCatalogContract.DIRECTION_REQUEST.equals(
                    direction)
                    ? CommunicationCatalogContract.requestPortId(
                    exchangeSiteKey, id)
                    : CommunicationCatalogContract.namedResponsePortId(
                    exchangeSiteKey, id);
        }

        CaptureSite client() {
            return CommunicationCatalogContract.DIRECTION_REQUEST.equals(
                    direction) ? producer : consumer;
        }

        CaptureSite server() {
            return CommunicationCatalogContract.DIRECTION_REQUEST.equals(
                    direction) ? consumer : producer;
        }

        Map<String, Object> row() {
            Map<String, Object> row = CommunicationCatalogPlanner.newRow(KIND);
            row.put("id", id);
            row.put(CommunicationCatalogContract.TRANSPORT, transport);
            row.put(CommunicationCatalogContract.PORT_DIRECTION, direction);
            row.put(CommunicationCatalogContract.PORT_JAVA_TYPE, javaType);
            row.put(CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                    exchangeSiteKey);
            row.put(CommunicationCatalogContract.PORT_ID, portId);
            row.put(CommunicationCatalogContract.PORT_NAME, id);
            row.put(CommunicationCatalogContract.CALL_SITE_ID,
                    client().siteId());
            row.put(CommunicationCatalogContract.CLIENT_METHOD,
                    client().method);
            row.put(CommunicationCatalogContract.SERVER_ENTRY_METHOD,
                    server().method);
            row.put(CommunicationCatalogContract.SERVER_ENTRY_CANDIDATES,
                    Collections.singletonList(server().method));
            row.put(PRODUCER, producer.row());
            row.put(CONSUMER, consumer.row());
            return row;
        }
    }

    static final class CaptureSite {
        static final String METHOD_PARAMETER = "METHOD_PARAMETER";
        static final String METHOD_RETURN = "METHOD_RETURN";
        static final String CALL_ARGUMENT = "CALL_ARGUMENT";
        static final String CALL_RETURN = "CALL_RETURN";

        final String method;
        final String kind;
        final int index;
        final String callee;
        final int unitIndex;
        final String javaType;
        final String frameMethod;

        private CaptureSite(String method, String kind, int index,
                            String callee, int unitIndex,
                            String javaType, String frameMethod) {
            this.method = method;
            this.kind = kind;
            this.index = index;
            this.callee = callee;
            this.unitIndex = unitIndex;
            this.javaType = javaType;
            this.frameMethod = frameMethod;
        }

        private static CaptureSite parse(JsonObject row,
                                         Map<String, SootMethod> methods,
                                         String frameMethod) {
            String methodName = string(row, "method");
            String kind = string(row, "kind").toUpperCase();
            int index = integer(row, "index", -1);
            String callee = string(row, "callee");
            int occurrence = integer(row, "occurrence", -1);
            SootMethod method = methods.get(methodName);
            if (method == null || !method.isConcrete()) {
                throw new IllegalArgumentException(
                        "capture method did not resolve: " + methodName);
            }
            if (METHOD_PARAMETER.equals(kind)) {
                if (index < 0 || index >= method.getParameterCount()
                        || !callee.isEmpty() || occurrence >= 0) {
                    throw new IllegalArgumentException(
                            "METHOD_PARAMETER requires only a valid index");
                }
                return new CaptureSite(methodName, kind, index, "", -1,
                        method.getParameterType(index).toString(),
                        frameMethod);
            }
            if (METHOD_RETURN.equals(kind)) {
                if (index >= 0 || !callee.isEmpty() || occurrence >= 0
                        || "void".equals(method.getReturnType().toString())) {
                    throw new IllegalArgumentException(
                            "METHOD_RETURN takes no selector");
                }
                return new CaptureSite(methodName, kind, -1, "", -1,
                        method.getReturnType().toString(), frameMethod);
            }
            if (!(CALL_ARGUMENT.equals(kind) || CALL_RETURN.equals(kind))
                    || callee.isEmpty() || occurrence < 0
                    || (CALL_ARGUMENT.equals(kind) && index < 0)
                    || (CALL_RETURN.equals(kind) && index >= 0)) {
                throw new IllegalArgumentException(
                        "call capture requires callee, occurrence and the correct index");
            }
            Body body = CausynthStaticFacts.activeBody(method);
            int seen = 0;
            int unitIndex = -1;
            Type type = null;
            int current = -1;
            for (Unit unit : body.getUnits()) {
                current++;
                if (!(unit instanceof Stmt)
                        || !((Stmt) unit).containsInvokeExpr()
                        || !callee.equals(((Stmt) unit).getInvokeExpr()
                        .getMethodRef().getSignature())) continue;
                if (seen++ != occurrence) continue;
                Stmt statement = (Stmt) unit;
                if (CALL_ARGUMENT.equals(kind)) {
                    if (index >= statement.getInvokeExpr().getArgCount()) {
                        throw new IllegalArgumentException(
                                "call argument index is out of range");
                    }
                    type = statement.getInvokeExpr().getArg(index).getType();
                } else {
                    type = statement.getInvokeExpr().getMethodRef()
                            .returnType();
                    if ("void".equals(type.toString())) {
                        throw new IllegalArgumentException(
                                "CALL_RETURN cannot capture void");
                    }
                }
                unitIndex = current;
                break;
            }
            if (unitIndex < 0 || type == null) {
                throw new IllegalArgumentException("call capture did not resolve: "
                        + methodName + " -> " + callee + " #" + occurrence);
            }
            return new CaptureSite(methodName, kind, index, callee,
                    unitIndex, type.toString(), frameMethod);
        }

        String siteId() {
            return unitIndex < 0 ? method
                    : SiteId.of(method, unitIndex);
        }

        Map<String, Object> row() {
            Map<String, Object> row = new LinkedHashMap<>();
            row.put(CommunicationCatalogContract.CALL_SITE_ID, siteId());
            row.put(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                    method);
            if (!frameMethod.isEmpty()) {
                row.put(CommunicationCatalogContract.PORT_FRAME_METHOD,
                        frameMethod);
            }
            row.put(CommunicationCatalogContract.PORT_OUTPUT_CAPTURE_KIND,
                    kind);
            if (unitIndex >= 0) {
                row.put(CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX,
                        unitIndex);
                row.put(CommunicationCatalogContract.DECLARED_CALLEE, callee);
            }
            if (index >= 0) {
                row.put(CommunicationCatalogContract.PORT_ARGUMENT_INDEX,
                        index);
            }
            return row;
        }
    }
}
