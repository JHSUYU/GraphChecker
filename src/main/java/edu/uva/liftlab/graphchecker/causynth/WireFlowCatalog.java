package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.SiteId;
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

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;

/**
 * The values messages carry, one port per value: a port is one carried value
 * with every capture that writes it and every capture that reads it.  A
 * declared row states one of each; direction and transport are no part of
 * it, since the recording binds each capture to the exchange it ran in and
 * replay keys everything on the port id.
 */
public final class WireFlowCatalog {
    static final String PROPERTY = "causynth.communication.mappings";
    static final String KIND = "WIRE_FLOW";
    static final int SCHEMA_VERSION = 2;

    private final List<WireFlow> flows;

    private WireFlowCatalog(List<WireFlow> flows) {
        this.flows = Collections.unmodifiableList(new ArrayList<>(flows));
    }

    static WireFlowCatalog fromConfiguration(
            Map<String, SootMethod> methods) throws IOException {
        List<WireFlow> flows = new ArrayList<>();
        for (Row row : rows()) {
            if (!applies(row.json, methods)) {
                System.err.println("causynth: communication mapping "
                        + string(row.json, "id") + " (" + row.at + ") names a"
                        + " method this program does not hold: not this"
                        + " program's flow");
                continue;
            }
            try {
                flows.add(parse(row.json, methods));
            } catch (RuntimeException invalid) {
                throw new IOException("Invalid communication mapping at "
                        + row.at + ": " + invalid.getMessage(), invalid);
            }
        }
        return new WireFlowCatalog(flows);
    }

    /**
     * Whether a declared flow is this program's: a system's mapping file
     * declares its protocol's flows once for every case, and a flow joins a
     * producer and a consumer, so a program that does not hold every method
     * a row names (producer, consumer, frame methods; concrete) carries
     * none of its values end to end.  Such a row is skipped by name in the
     * static pass's log; a row the program holds whole is parsed, and
     * refused by name if it is malformed.
     */
    static boolean applies(JsonObject row, Map<String, SootMethod> methods) {
        List<String> named = new ArrayList<>();
        for (String side : new String[] {"producer", "consumer"}) {
            JsonElement capture = row.get(side);
            if (capture != null && capture.isJsonObject()) {
                named.add(string(capture.getAsJsonObject(), "method"));
            }
            named.add(string(row, side + "FrameMethod"));
        }
        for (String method : named) {
            if (method.isEmpty()) continue;
            SootMethod held = methods.get(method);
            if (held == null || !held.isConcrete()) return false;
        }
        return true;
    }

    private static final class Row {
        final String at;
        final JsonObject json;

        Row(String at, JsonObject json) {
            this.at = at;
            this.json = json;
        }
    }

    /** The mapping file's rows, read once; none when the case maps nothing. */
    private static volatile List<Row> rows;

    private static List<Row> rows() throws IOException {
        List<Row> known = rows;
        if (known != null) return known;
        List<Row> read = new ArrayList<>();
        String configured = firstNonBlank(System.getProperty(PROPERTY));
        if (!configured.isEmpty()) {
            Path path = Paths.get(configured).toAbsolutePath().normalize();
            if (!Files.isRegularFile(path)) {
                throw new IOException("Communication mapping not found: "
                        + path);
            }
            try (BufferedReader reader = Files.newBufferedReader(path,
                    StandardCharsets.UTF_8)) {
                String line;
                int lineNumber = 0;
                while ((line = reader.readLine()) != null) {
                    lineNumber++;
                    if (line.trim().isEmpty()) continue;
                    String at = path + ":" + lineNumber;
                    JsonElement parsed;
                    try {
                        parsed = JsonParser.parseString(line);
                    } catch (RuntimeException invalid) {
                        throw new IOException("Invalid communication mapping"
                                + " at " + at + ": " + invalid.getMessage(),
                                invalid);
                    }
                    if (!parsed.isJsonObject()) {
                        throw new IOException("Invalid communication mapping"
                                + " at " + at + ": mapping must be an object");
                    }
                    read.add(new Row(at, parsed.getAsJsonObject()));
                }
            }
        }
        rows = Collections.unmodifiableList(read);
        return rows;
    }

    List<WireFlow> flows() {
        return flows;
    }

    /** Whether a declared port holds a capture at {@code site}: it is that
     *  port's, and no rule derives another there. */
    boolean captures(CaptureSite site) {
        for (WireFlow flow : flows) {
            if (flow.captures(site)) return true;
        }
        return false;
    }

    private static WireFlow parse(JsonObject row,
                                  Map<String, SootMethod> methods) {
        if (integer(row, "schemaVersion", -1) != SCHEMA_VERSION
                || !KIND.equals(string(row, "kind"))) {
            // Refused, never skipped: a skipped flow reads as "never sent".
            throw new IllegalArgumentException(
                    "communication mapping " + string(row, "id")
                            + " states schemaVersion "
                            + integer(row, "schemaVersion", -1) + " kind "
                            + string(row, "kind") + "; this build reads"
                            + " schemaVersion " + SCHEMA_VERSION + " kind "
                            + KIND);
        }
        String id = string(row, "id");
        String javaType = string(row, "javaType");
        if (id.isEmpty() || javaType.isEmpty()) {
            throw new IllegalArgumentException(
                    "wire flow requires id and javaType");
        }
        CaptureSite producer = CaptureSite.parse(object(row, "producer"),
                methods, frameMethod(row, "producerFrameMethod", methods));
        CaptureSite consumer = CaptureSite.parse(object(row, "consumer"),
                methods, frameMethod(row, "consumerFrameMethod", methods));
        if (!javaType.equals(producer.javaType)
                || !javaType.equals(consumer.javaType)) {
            throw new IllegalArgumentException("wire endpoint types differ for "
                    + id + ": " + producer.javaType + " -> "
                    + consumer.javaType + " (declared " + javaType + ")");
        }
        WireFlow flow = new WireFlow(id, id, javaType);
        flow.producers.add(producer);
        flow.consumers.add(consumer);
        return flow;
    }

    /**
     * One side's declared frame method, or "" (the RPC message is the frame).
     * One call of it builds one value instance, so same-shaped groups in one
     * message stay apart.
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

    /**
     * One port: every producer exports into {@link #portId} and every
     * consumer attaches from it, so a capture site belongs to one port.
     */
    static final class WireFlow {
        final String id;
        final String javaType;
        final String exchangeSiteKey;
        final String portId;
        final List<CaptureSite> producers = new ArrayList<>();
        final List<CaptureSite> consumers = new ArrayList<>();

        /** A port named {@code id}, keyed by {@code identity}. */
        WireFlow(String id, String identity, String javaType) {
            this.id = id;
            this.javaType = javaType;
            exchangeSiteKey = CommunicationCatalogContract.exchangeSiteKey(
                    identity);
            portId = CommunicationCatalogContract.portId(exchangeSiteKey, id);
        }

        boolean captures(CaptureSite site) {
            for (CaptureSite held : producers) {
                if (held.site().equals(site.site())) return true;
            }
            for (CaptureSite held : consumers) {
                if (held.site().equals(site.site())) return true;
            }
            return false;
        }

        Map<String, Object> row() {
            Map<String, Object> row = CommunicationCatalogPlanner.newRow(KIND);
            row.put("id", id);
            row.put(CommunicationCatalogContract.PORT_JAVA_TYPE, javaType);
            row.put(CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                    exchangeSiteKey);
            row.put(CommunicationCatalogContract.PORT_ID, portId);
            row.put(CommunicationCatalogContract.PORT_NAME, id);
            row.put(CommunicationCatalogContract.PORT_PRODUCERS,
                    rows(producers));
            row.put(CommunicationCatalogContract.PORT_CONSUMERS,
                    rows(consumers));
            return row;
        }

        /** In site order: a derived port gains consumers in worklist order. */
        private static List<Map<String, Object>> rows(
                List<CaptureSite> captures) {
            List<CaptureSite> ordered = new ArrayList<>(captures);
            ordered.sort(java.util.Comparator.comparing(CaptureSite::site));
            List<Map<String, Object>> rows = new ArrayList<>();
            for (CaptureSite capture : ordered) rows.add(capture.row());
            return rows;
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

        /** A call capture a rule found, framed by its RPC message. */
        static CaptureSite call(String method, String kind, int index,
                                String callee, int unitIndex,
                                String javaType) {
            return new CaptureSite(method, kind, index, callee, unitIndex,
                    javaType, "");
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

        /** Where the capture is: its site, kind and argument. */
        String site() {
            return kind + "@" + siteId() + "#" + index;
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
