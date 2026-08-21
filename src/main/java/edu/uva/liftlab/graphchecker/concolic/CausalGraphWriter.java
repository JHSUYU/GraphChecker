package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Draws the one canonical session model, and nothing else.
 *
 * <p>This writer used to build its own causal reading: it walked the runtime
 * plan's resolved edge catalog, re-derived an evidence state per edge from
 * whatever the trace had stamped on it, and merged the results into a graph the
 * composed formula had never seen. Two independent readings of one run is the
 * failure this phase removes, so the reconstruction is gone. Every node here
 * comes from {@link CanonicalSessionModel}'s node table, every edge from one of
 * its value bindings, order relations or structural rows, and the evidence
 * state on the drawing is the state the model already carries.</p>
 *
 * <p>A solver result is an overlay and never a source: when one exists its
 * selected read-from arms are marked and its verdict is reported; when none
 * exists nothing is marked. The graph is diagnostic and cannot accept or
 * reject the Composer's model.</p>
 */
public final class CausalGraphWriter {
    /** The projected causal model. */
    static final String MODEL_JSON = "causal_model.json";
    /** The rendering of that same model. */
    static final String MODEL_DOT = "causal_model.dot";
    /** The optional vector rendering of the same {@code .dot}. */
    static final String MODEL_SVG = "causal.svg";

    static final String USAGE =
            "usage: composed-manifest output-dir [solver-result]";

    /** The input carried no canonical model to project. */
    static final String NO_CANONICAL_MODEL =
            "composed manifest carries no canonical session model";

    /** No renderer is installed, so no SVG was produced. */
    static final String SVG_SKIPPED = "SKIPPED_NO_RENDERER";
    /** The renderer ran and produced the SVG. */
    static final String SVG_RENDERED = "RENDERED";
    /** A renderer exists and refused this graph. */
    static final String SVG_FAILED = "RENDERER_FAILED";

    private static final String OVERLAY_PRESENT = "SOLVER_MODEL_PRESENT";
    private static final String OVERLAY_ABSENT = "NO_SOLVER_MODEL";
    private static final String VALUE_BINDING = "VALUE_BINDING";
    private static final String ORDER_RELATION = "ORDER_RELATION";
    private static final String STRUCTURE = "STRUCTURE";

    private CausalGraphWriter() {
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 2) throw new IllegalArgumentException(USAGE);
        JsonObject composed = ArtifactIO.readObject(Paths.get(args[0]));
        JsonObject model = CanonicalSessionModel.read(composed);
        if (model.size() == 0) {
            throw new IllegalArgumentException(NO_CANONICAL_MODEL);
        }
        JsonObject solver = args.length > 2
                ? ArtifactIO.readObject(Paths.get(args[2])) : new JsonObject();

        JsonObject graph = graph(model, solver);
        String dot = dot(graph);
        Svg svg = render(dot);
        Path out = Paths.get(args[1]);
        graph.add("runManifest", runManifest(graph, model, composed, solver,
                dot, svg, out));
        JsonObject rendered = (JsonObject) CanonicalJson.copy(graph);

        ArtifactIO.replace(out.resolve(MODEL_JSON), new GsonBuilder()
                .disableHtmlEscaping().setPrettyPrinting().create()
                .toJson(rendered) + "\n");
        ArtifactIO.replace(out.resolve(MODEL_DOT), dot);
        if (svg.bytes.length > 0) {
            Files.createDirectories(out.toAbsolutePath().normalize());
            Files.write(out.resolve(MODEL_SVG), svg.bytes);
        }
    }

    /**
     * Projects the canonical model, overlaying a solver result if one exists.
     *
     * @param model  the canonical session model
     * @param solver the solver result, or an empty object
     */
    static JsonObject graph(JsonObject model, JsonObject solver) {
        Set<String> selectedArms = selectedArms(solver);
        Map<String, JsonObject> nodes = new LinkedHashMap<>();
        for (JsonElement element : array(model, "nodes")) {
            JsonObject row = element.getAsJsonObject().deepCopy();
            row.addProperty("label", label(row));
            row.addProperty("shape", shape(string(row, "nodeType")));
            nodes.put(string(row, "nodeId"), row);
        }
        List<JsonObject> edges = new ArrayList<>();
        for (JsonElement element : array(model, "valueBindings")) {
            edges.add(valueEdge(element.getAsJsonObject(), selectedArms));
        }
        for (JsonElement element : array(model, "eventOrder")) {
            edges.add(orderEdge(element.getAsJsonObject()));
        }
        for (JsonElement element : array(model, "structuralEdges")) {
            edges.add(structuralEdge(element.getAsJsonObject()));
        }

        JsonObject graph = new JsonObject();
        graph.addProperty("schemaVersion", 3);
        graph.addProperty("kind", "CAUSAL_MODEL");
        graph.addProperty("authority",
                "CANONICAL_SESSION_MODEL_PROJECTION_V1");
        JsonObject projection = new JsonObject();
        projection.addProperty("sourceKind", CanonicalSessionModel.KIND);
        projection.addProperty("sourceAuthority",
                CanonicalSessionModel.AUTHORITY);
        projection.addProperty("reDerivesEvidence", false);
        graph.add("projection", projection);
        graph.add("target", object(model, "target").deepCopy());
        graph.add("solverOverlay", overlay(solver, selectedArms));
        graph.addProperty("verdict", verdict(solver));
        JsonArray nodeRows = new JsonArray();
        for (JsonObject row : nodes.values()) nodeRows.add(row);
        graph.add("nodes", nodeRows);
        JsonArray edgeRows = new JsonArray();
        for (JsonObject row : edges) edgeRows.add(row);
        graph.add("edges", edgeRows);
        graph.add("coverage", coverage(model, edges, selectedArms));
        graph.add("gaps", array(model, "gaps").deepCopy());
        return graph;
    }

    // ----- edges ----------------------------------------------------------

    /**
     * One value binding, drawn once.
     *
     * <p>The evidence state is copied, never recomputed: the model already
     * decided whether the run proved this writer, guarded it, kept an unknown
     * arm, or only ever resolved a trace candidate, and a second opinion here
     * is exactly the divergence the audit exists to catch.</p>
     */
    private static JsonObject valueEdge(JsonObject binding,
                                        Set<String> selectedArms) {
        JsonObject edge = binding.deepCopy();
        String state = string(binding, "evidenceState");
        edge.addProperty("projection", VALUE_BINDING);
        edge.addProperty("graphEdgeId", string(binding, "bindingId"));
        edge.addProperty("bindingKind", string(binding, "kind"));
        edge.addProperty("kind", edgeKind(string(binding, "kind")));
        edge.addProperty("from", string(binding, "fromNodeId"));
        edge.addProperty("to", string(binding, "toNodeId"));
        boolean selected = !selectedArms.isEmpty()
                && selectedArms.contains(longInteger(binding, "readEventId",
                0L) + "\n" + string(binding, "arm"));
        edge.addProperty("selected", selected);
        style(edge, state, selected);
        return edge;
    }

    private static JsonObject orderEdge(JsonObject relation) {
        JsonObject edge = relation.deepCopy();
        edge.addProperty("projection", ORDER_RELATION);
        edge.addProperty("graphEdgeId", string(relation, "relationId"));
        edge.addProperty("kind", "RECORDED_ORDER");
        edge.addProperty("from", string(relation, "fromNodeId"));
        edge.addProperty("to", string(relation, "toNodeId"));
        edge.addProperty("selected", false);
        style(edge, CanonicalSessionModel.NATURAL_ORDER, false);
        return edge;
    }

    private static JsonObject structuralEdge(JsonObject row) {
        JsonObject edge = row.deepCopy();
        edge.addProperty("projection", STRUCTURE);
        edge.addProperty("graphEdgeId", string(row, "structuralId"));
        edge.addProperty("from", string(row, "fromNodeId"));
        edge.addProperty("to", string(row, "toNodeId"));
        edge.addProperty("selected", false);
        style(edge, CanonicalSessionModel.STRUCTURAL, false);
        return edge;
    }

    /** The short kind one binding row is drawn under. */
    private static String edgeKind(String bindingKind) {
        if ("RECORDED_READ_FROM_VALUE_BINDING".equals(bindingKind)) {
            return "READ_FROM_ARM";
        }
        if ("RECORDED_EXACT_VALUE_BINDING".equals(bindingKind)) {
            return "EXACT_VALUE";
        }
        if ("RECORDED_GUARDED_READ_PORT_BINDING".equals(bindingKind)) {
            return "GUARDED_READ_PORT";
        }
        if (VmHandoffEvidence.BINDING_KIND.equals(bindingKind)) {
            return "HANDOFF_EQUALITY";
        }
        return "RESOLVED_CANDIDATE";
    }

    /**
     * The one place an evidence state becomes something visible.
     *
     * <p>Five states, five distinguishable pens. They differ in dash pattern
     * and in colour, so the drawing stays readable when it is printed without
     * colour and when it is read by someone who does not see the hues apart.
     * </p>
     */
    private static void style(JsonObject edge, String state,
                              boolean selected) {
        String style;
        String colour;
        if (CanonicalSessionModel.EXACT.equals(state)) {
            style = "solid";
            colour = "#1a7f37";
        } else if (CanonicalSessionModel.GUARDED.equals(state)) {
            style = "dashed";
            colour = "#0969da";
        } else if (CanonicalSessionModel.UNKNOWN_ARM.equals(state)) {
            style = "dotted";
            colour = "#9a6700";
        } else if (CanonicalSessionModel.NATURAL_ORDER.equals(state)) {
            style = "solid";
            colour = "#57606a";
        } else if (CanonicalSessionModel.CANDIDATE.equals(state)) {
            style = "dotted";
            colour = "#8250df";
        } else {
            style = "solid";
            colour = "#8c959f";
        }
        edge.addProperty("evidenceState", state);
        edge.addProperty("style", style);
        edge.addProperty("color", colour);
        edge.addProperty("penwidth", selected ? 3
                : CanonicalSessionModel.EXACT.equals(state) ? 2 : 1);
        edge.addProperty("label", string(edge, "kind") + "\n" + state
                + (selected ? "\nSELECTED" : ""));
    }

    // ----- solver overlay -------------------------------------------------

    /** The {@code readEventId\narm} pairs one solver model selected. */
    private static Set<String> selectedArms(JsonObject solver) {
        Set<String> arms = new LinkedHashSet<>();
        for (JsonElement element : array(object(solver, "selectedReadCut"),
                "selections")) {
            if (!element.isJsonObject()) continue;
            JsonObject row = element.getAsJsonObject();
            arms.add(longInteger(row, "readEventId", 0L) + "\n"
                    + string(row, "arm"));
        }
        return arms;
    }

    /**
     * What the solver said, and nothing more.
     *
     * <p>An absent result is reported as an absent result. Reading a verdict
     * out of a missing file - or marking an arm because only one arm exists -
     * would be the drawing claiming a decision nobody made.</p>
     */
    private static JsonObject overlay(JsonObject solver,
                                      Set<String> selectedArms) {
        JsonObject overlay = new JsonObject();
        boolean present = solver != null && solver.size() > 0;
        overlay.addProperty("state", present ? OVERLAY_PRESENT
                : OVERLAY_ABSENT);
        overlay.addProperty("selectedArmCount", selectedArms.size());
        overlay.addProperty("solverStatus", present
                ? string(solver, "status") : "");
        overlay.add("reachCondition", present
                ? object(solver, "reachCondition").deepCopy()
                : new JsonObject());
        overlay.add("selections", present
                ? array(object(solver, "selectedReadCut"), "selections")
                .deepCopy() : new JsonArray());
        overlay.add("rootAssignments", present ? assignments(solver)
                : new JsonArray());
        return overlay;
    }

    private static String verdict(JsonObject solver) {
        if (solver == null || solver.size() == 0) return OVERLAY_ABSENT;
        String reachable = string(object(solver, "reachCondition"),
                "reachability");
        if ("REACHABLE".equals(reachable)) return "SAT";
        if ("UNREACHABLE".equals(reachable)) return "UNSAT";
        String status = string(solver, "status");
        if ("SAT_MODEL_READY".equals(status)) return "SAT";
        if ("UNSAT".equals(status)) return "UNSAT";
        return "UNKNOWN";
    }

    /** The root inputs one satisfiable valuation assigned. */
    private static JsonArray assignments(JsonObject solver) {
        JsonArray result = new JsonArray();
        JsonArray roots = array(object(solver, "roots"), "booleanInputs");
        for (JsonElement element : array(solver, "valuations")) {
            if (!element.isJsonObject() || !"sat".equals(
                    string(element.getAsJsonObject(), "status"))) {
                continue;
            }
            JsonArray values = array(element.getAsJsonObject(), "values");
            for (int index = 0;
                 index < Math.min(roots.size(), values.size()); index++) {
                if (!roots.get(index).isJsonObject()) continue;
                JsonObject root = roots.get(index).getAsJsonObject();
                JsonObject row = new JsonObject();
                for (String field : new String[]{"portId", "solverTerm",
                        "javaTypeDescriptor"}) {
                    if (root.has(field)) {
                        row.add(field, root.get(field).deepCopy());
                    }
                }
                row.add("value", values.get(index).deepCopy());
                result.add(row);
            }
            break;
        }
        return result;
    }

    // ----- coverage and run manifest --------------------------------------

    private static JsonObject coverage(JsonObject model,
                                       List<JsonObject> edges,
                                       Set<String> selectedArms) {
        Map<String, Integer> states = new LinkedHashMap<>();
        for (JsonObject edge : edges) {
            String state = string(edge, "evidenceState");
            Integer held = states.get(state);
            states.put(state, held == null ? 1 : held + 1);
        }
        JsonObject coverage = new JsonObject();
        coverage.add("modelCounts", object(model, "counts").deepCopy());
        JsonObject byState = new JsonObject();
        for (String state : new String[]{CanonicalSessionModel.EXACT,
                CanonicalSessionModel.GUARDED,
                CanonicalSessionModel.UNKNOWN_ARM,
                CanonicalSessionModel.NATURAL_ORDER,
                CanonicalSessionModel.CANDIDATE,
                CanonicalSessionModel.STRUCTURAL}) {
            byState.addProperty(state, states.containsKey(state)
                    ? states.get(state) : 0);
        }
        coverage.add("edgesByEvidenceState", byState);
        coverage.addProperty("selectedArms", selectedArms.size());
        coverage.addProperty("gapCount", array(model, "gaps").size());
        coverage.addProperty("partial",
                bool(object(model, "target"), "partial", false));
        return coverage;
    }

    /**
     * The one run manifest: what was projected, and what each artifact is.
     *
     * <p>{@code causal_model.json} is the file this member lives in, so it
     * cannot hold its own digest; it holds the digest of everything it was
     * made from and everything it generates instead.</p>
     */
    private static JsonObject runManifest(JsonObject graph, JsonObject model,
                                          JsonObject composed,
                                          JsonObject solver, String dot,
                                          Svg svg, Path out) {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 1);
        manifest.addProperty("kind", "CAUSAL_GRAPH_RUN_MANIFEST");
        manifest.addProperty("authority",
                "CANONICAL_SESSION_MODEL_PROJECTION_V1");
        JsonObject counts = new JsonObject();
        counts.addProperty("nodes", array(graph, "nodes").size());
        counts.addProperty("edges", array(graph, "edges").size());
        counts.addProperty("valueBindingEdges",
                projected(graph, VALUE_BINDING));
        counts.addProperty("orderRelationEdges",
                projected(graph, ORDER_RELATION));
        counts.addProperty("structuralEdges",
                projected(graph, STRUCTURE));
        counts.addProperty("smtValueBindings",
                array(composed, "recordedValueBindings").size());
        counts.addProperty("resolvedEdgeBindings",
                array(composed, "resolvedEdgeBindings").size());
        counts.addProperty("recordedOrderRelations",
                array(object(composed, "recordedSessionModel"),
                        "order").size());
        counts.addProperty("selectedArms",
                array(object(solver, "selectedReadCut"), "selections")
                        .size());
        counts.addProperty("gaps", array(graph, "gaps").size());
        manifest.add("counts", counts);
        JsonArray artifacts = new JsonArray();
        artifacts.add(digest("canonicalModel", CanonicalJson.sha256(model)));
        artifacts.add(digest("composedSmtManifest",
                CanonicalJson.sha256(composed)));
        artifacts.add(digest("candidateSmt", string(object(composed,
                "composedSmtArtifact"), "sha256")));
        artifacts.add(digest("solverResult", solver.size() == 0 ? ""
                : CanonicalJson.sha256(solver)));
        artifacts.add(path(digest(MODEL_DOT, ArtifactIO.sha256(dot)), out,
                MODEL_DOT));
        JsonObject svgRow = digest(MODEL_SVG, svg.bytes.length == 0 ? ""
                : ArtifactIO.sha256(svg.bytes));
        if (svg.bytes.length > 0) path(svgRow, out, MODEL_SVG);
        artifacts.add(svgRow);
        manifest.add("artifacts", artifacts);
        manifest.addProperty("svg", svg.state);
        return manifest;
    }

    private static JsonObject digest(String name, String sha256) {
        JsonObject row = new JsonObject();
        row.addProperty("name", name);
        row.addProperty("sha256", sha256);
        return row;
    }

    private static JsonObject path(JsonObject row, Path out, String name) {
        row.addProperty("path", out.toAbsolutePath().normalize()
                .resolve(name).toString());
        return row;
    }

    private static int projected(JsonObject graph, String projection) {
        int count = 0;
        for (JsonElement element : array(graph, "edges")) {
            if (projection.equals(string(element.getAsJsonObject(),
                    "projection"))) {
                count++;
            }
        }
        return count;
    }

    // ----- rendering ------------------------------------------------------

    static String dot(JsonObject graph) {
        StringBuilder out = new StringBuilder(
                "digraph causal_model {\n  rankdir=LR;\n"
                        + "  node [fontname=\"Helvetica\"];\n"
                        + "  edge [fontname=\"Helvetica\", fontsize=9];\n");
        for (JsonElement element : array(graph, "nodes")) {
            JsonObject node = element.getAsJsonObject();
            out.append("  \"").append(escape(string(node, "nodeId")))
                    .append("\" [shape=").append(string(node, "shape"))
                    .append(", label=\"").append(escape(string(node, "label")))
                    .append("\"];\n");
        }
        for (JsonElement element : array(graph, "edges")) {
            JsonObject edge = element.getAsJsonObject();
            out.append("  \"").append(escape(string(edge, "from")))
                    .append("\" -> \"").append(escape(string(edge, "to")))
                    .append("\" [style=")
                    .append(firstNonBlank(string(edge, "style"), "solid"))
                    .append(", color=\"").append(string(edge, "color"))
                    .append("\", penwidth=")
                    .append(JsonFields.integer(edge, "penwidth", 1))
                    .append(", label=\"")
                    .append(escape(string(edge, "label"))).append("\"];\n");
        }
        return out.append("}\n").toString();
    }

    /**
     * Renders the SVG when a renderer is installed, and otherwise not.
     *
     * <p>Best effort in both directions: a machine with Graphviz gets the
     * vector drawing, a machine without one gets a recorded skip. Neither a
     * missing binary nor a renderer that refuses the graph fails the run,
     * because the SVG is a convenience and the {@code .dot} is the artifact.
     * No layout engine is reimplemented here - a hand-rolled one would draw a
     * different picture from the one Graphviz draws elsewhere.</p>
     */
    static Svg render(String dot) {
        if (!hasRenderer()) return new Svg(new byte[0], SVG_SKIPPED);
        try {
            Process process = new ProcessBuilder("dot", "-Tsvg")
                    .redirectErrorStream(false).start();
            try (OutputStream input = process.getOutputStream()) {
                input.write(dot.getBytes(StandardCharsets.UTF_8));
            }
            byte[] svg = readAll(process.getInputStream());
            if (!process.waitFor(30L, TimeUnit.SECONDS)) {
                process.destroyForcibly();
                return new Svg(new byte[0], SVG_FAILED);
            }
            return process.exitValue() == 0 && svg.length > 0
                    ? new Svg(svg, SVG_RENDERED)
                    : new Svg(new byte[0], SVG_FAILED);
        } catch (Exception unavailable) {
            return new Svg(new byte[0], SVG_FAILED);
        }
    }

    /** The optional vector rendering, and why it is or is not there. */
    static final class Svg {
        final byte[] bytes;
        final String state;

        private Svg(byte[] bytes, String state) {
            this.bytes = bytes;
            this.state = state;
        }
    }

    private static boolean hasRenderer() {
        try {
            Process probe = new ProcessBuilder("dot", "-V")
                    .redirectErrorStream(true).start();
            readAll(probe.getInputStream());
            return probe.waitFor(10L, TimeUnit.SECONDS)
                    && probe.exitValue() == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }

    private static byte[] readAll(InputStream stream) throws java.io.IOException {
        ByteArrayOutputStream buffer = new ByteArrayOutputStream();
        byte[] chunk = new byte[8192];
        int read;
        while ((read = stream.read(chunk)) >= 0) buffer.write(chunk, 0, read);
        return buffer.toByteArray();
    }

    // ----- labels ---------------------------------------------------------

    private static String label(JsonObject node) {
        String type = string(node, "nodeType");
        if (CanonicalSessionModel.NODE_SOURCE.equals(type)) {
            return string(node, "sourceKey");
        }
        if (CanonicalSessionModel.NODE_REGION.equals(type)) {
            return firstNonBlank(string(node, "regionId"), "region") + "\n"
                    + string(node, "occurrenceId");
        }
        boolean mapState = SharedStateEvidence.LOCATION_KIND_MAP_STATE
                .equals(string(node, "locationKind"));
        if (CanonicalSessionModel.NODE_FIELD_VERSION.equals(type)) {
            // A map mutation publishes a whole immutable state, not a value,
            // and the drawing says which so a reader is not left to infer the
            // difference from the location key.
            return (mapState ? "map state #" : "write #")
                    + longInteger(node, "eventId", 0L) + "\n"
                    + string(node, "locationKey");
        }
        if (CanonicalSessionModel.NODE_FIELD_READ.equals(type)) {
            return (mapState ? "map query #" : "read #")
                    + longInteger(node, "eventId", 0L) + "\n"
                    + string(node, "resolution");
        }
        if (CanonicalSessionModel.NODE_UNKNOWN_WRITER.equals(type)) {
            return "unknown writer\nread #"
                    + longInteger(node, "readEventId", 0L);
        }
        if (CanonicalSessionModel.NODE_SESSION_EVENT.equals(type)) {
            return "event #" + longInteger(node, "eventId", 0L);
        }
        return string(node, "siteId");
    }

    private static String shape(String type) {
        if (CanonicalSessionModel.NODE_SOURCE.equals(type)) return "oval";
        if (CanonicalSessionModel.NODE_REGION.equals(type)) return "box";
        if (CanonicalSessionModel.NODE_FIELD_VERSION.equals(type)) {
            return "parallelogram";
        }
        if (CanonicalSessionModel.NODE_FIELD_READ.equals(type)) {
            return "hexagon";
        }
        if (CanonicalSessionModel.NODE_UNKNOWN_WRITER.equals(type)) {
            return "octagon";
        }
        if (CanonicalSessionModel.NODE_TARGET_BRANCH.equals(type)) {
            return "diamond";
        }
        return "ellipse";
    }

    private static String escape(String value) {
        return (value == null ? "" : value).replace("\\", "\\\\")
                .replace("\"", "\\\"").replace("\r", "")
                .replace("\n", "\\n");
    }
}
