package edu.uva.liftlab.graphchecker.explore;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;
import edu.uva.liftlab.graphchecker.compose.ComposeMain;
import edu.uva.liftlab.graphchecker.compose.Refutations;
import edu.uva.liftlab.graphchecker.compose.RestsOn;
import edu.uva.liftlab.graphchecker.compose.SmtLowering;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.AttachRow;
import edu.uva.liftlab.graphchecker.contract.ContextShape;
import edu.uva.liftlab.graphchecker.contract.DecisionRow;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.ExportRow;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.Interaction;
import edu.uva.liftlab.graphchecker.contract.InteractionKind;
import edu.uva.liftlab.graphchecker.contract.LocationId;
import edu.uva.liftlab.graphchecker.contract.LocationKind;
import edu.uva.liftlab.graphchecker.contract.Obligation;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ReadRow;
import edu.uva.liftlab.graphchecker.contract.RowOrder;
import edu.uva.liftlab.graphchecker.contract.RootCategory;
import edu.uva.liftlab.graphchecker.contract.RootKind;
import edu.uva.liftlab.graphchecker.contract.RootMintRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.RunSpellings;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionManifest;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.contract.TargetRow;
import edu.uva.liftlab.graphchecker.contract.WriteRow;
import edu.uva.liftlab.graphchecker.option.LongOptions;
import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.runtime.Confirmation;
import edu.uva.liftlab.graphchecker.runtime.RecordingPlant;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.strings;

public final class ConfirmMain {
    static final String OBLIGATION_ID = "CONFIRM";
    static final String REALIZED = "realized.json";

    private ConfirmMain() {
    }

    public static void main(String[] argv) throws Exception {
        LongOptions options = LongOptions.parse(argv);
        Path iteration = options.path("iteration");
        Path claim = options.path("claim");
        Path manifest = options.path("manifest");
        Path out = options.path("output");
        Path sessions = options.path("sessions");
        Path plant = options.path("plant");
        Path scopeMap = options.path("static-scope-map");
        Path confirmed = options.path("confirmed-session");
        if (sessions != null && claim != null && out != null) {
            System.out.println(ExploreMain.pretty(
                    decide(claim, out, sessions)));
            return;
        }
        if (iteration == null || claim == null || manifest == null
                || (plant == null && out == null)
                || (plant != null && (scopeMap == null
                || confirmed == null))) {
            throw new IllegalArgumentException("--iteration, --claim, "
                    + "--manifest, and --output or --plant with "
                    + "--static-scope-map and --confirmed-session are "
                    + "required");
        }
        JsonObject summary;
        try {
            summary = plant != null
                    ? writePlant(iteration, claim, manifest, scopeMap,
                    confirmed, plant)
                    : write(iteration, claim, manifest, out);
        } catch (Refused refused) {
            System.err.println("CONFIRM " + (refused.refutes ? "refutes"
                    : "refused") + ": " + refused.getMessage());
            JsonObject row = new JsonObject();
            row.addProperty("kind", "CONFIRM_REFUSED");
            row.addProperty("refutes", refused.refutes);
            row.addProperty("reason", refused.getMessage());
            System.out.println(ExploreMain.pretty(row));
            System.exit(1);
            return;
        }
        System.out.println(ExploreMain.pretty(summary));
    }

    static final class Refused extends RuntimeException {
        final boolean refutes;

        Refused(String reason) {
            this(reason, false);
        }

        private Refused(String reason, boolean refutes) {
            super(reason);
            this.refutes = refutes;
        }

        static Refused noCounterfactual(String reason) {
            return new Refused(reason, true);
        }
    }

    static JsonObject write(Path iteration, Path claimFile,
                            Path manifestFile, Path out) throws IOException {
        Files.createDirectories(out);
        Witness witness = Witness.of(iteration,
                ExploreCodec.readObject(claimFile),
                ExploreCodec.readObject(manifestFile));
        if ((witness.sessionId.equals(witness.seedSessionId)
                || witness.session.forced())
                && object(witness.decided, "movedRoots").size() == 0
                && witness.repaired.isEmpty()
                && ownDeliveries(witness.sessionId, witness.arms)
                && witness.sawChosen) {
            throw Refused.noCounterfactual("the claim moves nothing: its "
                    + "witness is the run as recorded -- the seed's own "
                    + "path, every root and clock as recorded, every arm its "
                    + "own delivery -- so no run of it is a counterfactual");
        }
        String realized = realizedBy(witness.moved, witness.world,
                witness.sessionId, witness.arms, witness.session,
                witness.anchor, witness.sawChosen);
        if (!realized.isEmpty()) {
            RowCodec.writeJsonl(out.resolve(REALIZED),
                    Collections.singletonList(
                            confirmation(true, false, realized,
                                    witness.sessionId)));
            JsonObject summary = witness.summary();
            summary.addProperty("realizedBy", witness.sessionId);
            return summary;
        }

        World world = witness.planted();

        SchedulePrefix.Cut cut = SchedulePrefix.write(iteration,
                witness.session.forced() ? witness.seedSessionId
                        : witness.sessionId,
                Collections.singletonList(witness.anchor.id()), false, out);
        if (cut == null) {
            throw new Refused("the selected session " + witness.sessionId
                    + " states no schedule to hold the confirmation to");
        }
        List<JsonObject> edges = witness.edges(iteration, world);
        RowCodec.writeJsonl(out.resolve(Confirmation.FILE), edges);

        JsonObject focus = ExploreCodec.writeFocusRow(witness.anchor,
                witness.anchor, witness.seedSessionId,
                Collections.<OccurrenceAddress>emptyList(),
                Obligation.confirming(OBLIGATION_ID, OBLIGATION_ID,
                        witness.pathId, world.assignments, world.answers,
                        Collections.<String>emptyList()),
                Collections.<Corpus.Flip>emptyList(), world.clockDeltas,
                world.mints, Collections.<String, String>emptyMap(), cut);
        ExploreCodec.writeFocusFile(out.resolve(ObligationDir.FOCUSED_TASK),
                focus);

        JsonObject summary = witness.summary();
        summary.addProperty("rootAssignments", world.assignments.size());
        summary.addProperty("clockDeltas", world.clockDeltas.size());
        summary.addProperty("expectedEdges", edges.size());
        summary.addProperty("checkedOrders", checkedOrders(edges));
        summary.add("schedulePrefix", cut.toJson());
        return summary;
    }

    static final class Witness {
        final JsonObject decided;
        final JsonObject manifest;
        final int ordinal;
        final String pathId;
        final String sessionId;
        final String seedSessionId;
        final OccurrenceAddress anchor;
        final long cutoff;
        final List<JsonObject> arms;
        final SessionReader session;
        final SessionReader recording;
        final StateClosure closure;
        final Map<String, WriteRow> chosen;
        final Set<String> restsOn;
        final JsonObject world;
        final Moved moved;
        final boolean sawChosen;
        final Set<OccurrenceAddress> cone =
                new LinkedHashSet<OccurrenceAddress>();
        final Set<String> history = new LinkedHashSet<String>();
        final Set<String> chosenAt = new LinkedHashSet<String>();
        final List<String> repaired = new ArrayList<String>();

        private Witness(JsonObject claim, JsonObject manifest, Path iteration)
                throws IOException {
            this.manifest = manifest;
            decided = claim.getAsJsonObject("claim");
            ordinal = decided.get("valuationOrdinal").getAsInt();
            JsonObject valuation = valuation(claim, ordinal);
            pathId = optionalString(valuation, "selectedPathId");
            sessionId = optionalString(valuation, "selectedSessionId");
            if (pathId.isEmpty() || sessionId.isEmpty()) {
                throw new Refused("valuation " + ordinal
                        + " selected no path, so there is nothing to "
                        + "confirm");
            }
            anchor = OccurrenceAddress.parse(optionalString(claim, "anchor"));
            if (anchor == null) {
                throw new Refused("the claim states no parseable anchor");
            }
            seedSessionId = optionalString(claim, "seedSessionId");
            String ordinalOfPath = "";
            restsOn = new LinkedHashSet<String>();
            boolean stated = false;
            long decidedAt = -1L;
            for (JsonElement element : array(manifest, "paths")) {
                JsonObject path = element.getAsJsonObject();
                if (pathId.equals(optionalString(path, "pathId"))) {
                    ordinalOfPath = Refutations.ordinal(optionalString(path,
                            "selector"));
                    stated = path.has("restsOn");
                    restsOn.addAll(strings(path, "restsOn"));
                    decidedAt = path.has("cutoff")
                            ? path.get("cutoff").getAsLong() : -1L;
                }
            }
            cutoff = decidedAt;
            if (ordinalOfPath.isEmpty() || !stated || cutoff < 0L) {
                throw new Refused("the manifest states no selector, no "
                        + "restsOn or no cutoff for the selected path "
                        + pathId);
            }
            arms = new ArrayList<JsonObject>();
            for (JsonElement element : array(valuation, "selectedArms")) {
                JsonObject arm = element.getAsJsonObject();
                if (ordinalOfPath.equals(
                        Refutations.ordinal(optionalString(arm, "selector")))) {
                    arms.add(arm);
                }
            }
            for (String selector : strings(valuation, "repairedArms")) {
                if (ordinalOfPath.equals(Refutations.ordinal(selector))) {
                    repaired.add(selector);
                }
            }
            session = SessionReader.read(iteration, sessionId);
            recording = SessionReader.read(iteration, seedSessionId);
            closure = new StateClosure(session, anchor, cutoff);
            chosen = closure.chosen(arms);
            chosen.keySet().removeIf(reader -> !restsOn.contains(
                    SmtLowering.locationKey(closure.readers.get(reader)
                            .location())));
            for (String reader : chosen.keySet()) {
                chosenAt.add(SmtLowering.locationKey(
                        closure.readers.get(reader).location()));
            }
            for (JsonObject arm : arms) {
                String group = optionalString(arm, "groupId");
                if (optionalString(arm, "selector").startsWith(
                        "observed_arm__") && group.startsWith("observed:")) {
                    chosenAt.add(group.substring("observed:".length()));
                }
            }
            world = obligationWorld(iteration, sessionId);
            moved = moved(decided, manifest, session, recording);
            sawChosen = closure.ran(chosen);
        }

        static Witness of(Path iteration, JsonObject claim,
                          JsonObject manifest) throws IOException {
            return new Witness(claim, manifest, iteration);
        }

        World planted() {
            World planted = new World(world);
            moved.plant(planted.assignments, planted.clockDeltas,
                    planted.mints);
            return planted;
        }

        List<JsonObject> edges(Path iteration, World planted)
                throws IOException {
            Map<String, SessionReader> armSessions =
                    new LinkedHashMap<String, SessionReader>();
            armSessions.put(sessionId, session);
            for (JsonObject arm : arms) {
                String armSession = optionalString(arm, "sessionId");
                if (armSession.isEmpty()
                        || armSessions.containsKey(armSession)) {
                    continue;
                }
                armSessions.put(armSession, SessionReader.read(iteration,
                        armSession));
            }
            List<JsonObject> edges = new ArrayList<JsonObject>();
            cone.add(anchor);
            edges.addAll(wireEdges(arms, armSessions, anchor, cone));
            List<ReadRow> resting = new ArrayList<ReadRow>();
            for (ReadRow read : closure.readers.values()) {
                if (restsOn.contains(SmtLowering.locationKey(
                        read.location()))) {
                    resting.add(read);
                }
            }
            Holding state = stateEdges(closure, resting, chosen, chosenAt,
                    false);
            edges.addAll(state.edges);
            cone.addAll(state.cone);
            Holding pairings = holding(session, ExploreCodec.map(object(world,
                    "pairings")));
            edges.addAll(pairings.edges);
            cone.addAll(pairings.cone);
            history.addAll(state.history());
            history.removeAll(pairings.orders);
            heldOnce(edges);
            edges.addAll(markerEdges(manifest, planted.assignments));
            JsonObject anchorRow = new JsonObject();
            anchorRow.addProperty("kind", "ANCHOR");
            anchorRow.addProperty("occurrence", anchor.id());
            anchorRow.addProperty("seq", cutoff);
            edges.add(anchorRow);
            return edges;
        }

        Map<String, RootCategory> categories() {
            Map<String, RootCategory> categories =
                    new LinkedHashMap<String, RootCategory>();
            for (SessionReader rows : Arrays.asList(recording, session)) {
                for (RootMintRow row : rows.roots()) {
                    categories.putIfAbsent(row.rootId(), row.category());
                }
            }
            return categories;
        }

        JsonObject summary() {
            return ConfirmMain.summary(anchor, pathId, sessionId, ordinal);
        }
    }

    static final class World {
        final Map<String, String> assignments;
        final Map<String, String> clockDeltas;
        final Map<String, String> mints;
        final Map<String, String> answers;

        World(JsonObject focus) {
            assignments = ExploreCodec.map(object(focus, "rootAssignments"));
            clockDeltas = ExploreCodec.map(object(focus, "clockDeltas"));
            mints = ExploreCodec.map(object(focus, "rootMints"));
            answers = ExploreCodec.map(object(focus, "answers"));
        }
    }

    static JsonObject writePlant(Path iteration, Path claimFile,
                                 Path manifestFile, Path scopeMap,
                                 Path confirmedSession, Path out)
            throws IOException {
        JsonObject claim = ExploreCodec.readObject(claimFile);
        Witness witness = Witness.of(iteration, claim,
                ExploreCodec.readObject(manifestFile));
        World world = witness.planted();
        Map<String, RootCategory> categories = witness.categories();
        PlantSites sites = PlantSites.read(
                iteration.resolve("execution_task_plan.jsonl"));
        List<JsonObject> rows = new ArrayList<JsonObject>();
        for (Map.Entry<String, String> assigned
                : world.assignments.entrySet()) {
            String value = assigned.getValue().trim();
            RootCategory category = categories.get(assigned.getKey());
            if (category == RootCategory.FAULT && "false".equals(value)) {
                continue;
            }
            rows.add(assignedRoot(assigned.getKey(), value, category, world,
                    sites));
        }
        for (Map.Entry<String, String> skew : world.clockDeltas.entrySet()) {
            rows.add(clockRoot(skew.getKey(), skew.getValue().trim(), world,
                    sites));
        }
        if (!world.answers.isEmpty()) {
            rows.addAll(answers(world.answers, witness, sites));
        }
        Set<String> orders = new LinkedHashSet<String>();
        int placeholders = 0;
        for (JsonObject edge : witness.edges(iteration, world)) {
            String kind = optionalString(edge, "kind");
            if ("STATE".equals(kind) && edge.has("mint")
                    && edge.get("mint").getAsBoolean()) {
                placeholders++;
            }
            String order = optionalString(edge, "before") + "\n"
                    + optionalString(edge, "after");
            if (RecordingPlant.ORDER.equals(kind)
                    && !witness.history.contains(order) && orders.add(order)
                    || RecordingPlant.VIEW_HOLD.equals(kind)
                    && orders.add(edge.toString())) {
                rows.add(edge);
            }
        }
        if (!Files.isDirectory(confirmedSession)) {
            throw new Refused("the session CONFIRM saw (" + confirmedSession
                    + ") is not there, so its order cannot be held");
        }
        Set<OccurrenceAddress> mints = new LinkedHashSet<OccurrenceAddress>();
        for (JsonObject row : rows) {
            if (RecordingPlant.ROOT.equals(optionalString(row,
                    RecordingPlant.KIND))) {
                mints.add(mintOf(world, optionalString(row,
                        RecordingPlant.ROOT_ID)));
            }
        }
        List<JsonObject> realized = RealizedOrder.rows(SessionDir.of(
                confirmedSession.getParent().getParent(),
                confirmedSession.getFileName().toString()).schedule(), mints,
                witness.cone);
        rows.addAll(realized);
        if (rows.isEmpty()) {
            throw new Refused("NATIVE_PLANT_UNSUPPORTED: the world plants no "
                    + "root and holds no order the model chose, so a native "
                    + "run would repeat the recording");
        }
        int planted = rows.size();
        if (!world.clockDeltas.isEmpty()) {
            for (Map.Entry<PlantSites.Call, Set<String>> reading
                    : sites.clockReadings().entrySet()) {
                JsonObject row = callRow(RecordingPlant.CLOCK_SITE,
                        reading.getKey());
                row.add(RecordingPlant.REGIONS, textArray(reading.getValue()));
                rows.add(row);
            }
        }
        int context = rows.size();
        for (StaticScopeMap.Site target
                : StaticScopeMap.read(scopeMap).targetSites()) {
            for (int index = 0; index < target.guards.size()
                    && index < target.guardOutcomes.size(); index++) {
                if (target.guardOutcomes.get(index) == null) continue;
                JsonObject row = new JsonObject();
                row.addProperty(RecordingPlant.KIND, RecordingPlant.TARGET);
                row.addProperty(RecordingPlant.OCCURRENCE, witness.anchor.id());
                row.addProperty(RecordingPlant.SITE, target.guards.get(index));
                row.addProperty(RecordingPlant.VALUE,
                        target.guardOutcomes.get(index));
                rows.add(row);
            }
        }
        if (rows.size() == context) {
            throw new Refused("NATIVE_PLANT_UNSUPPORTED: " + scopeMap
                    + " states no fatal arm of a TARGET_SITE guard, so a "
                    + "native run could not tell whether it reproduced");
        }
        for (int index = 0; index < rows.size(); index++) {
            rows.get(index).addProperty(RecordingPlant.ROW, index);
        }
        RowCodec.writeJsonl(out, rows);
        JsonObject summary = witness.summary();
        summary.addProperty("roots", world.assignments.size());
        summary.addProperty("clocks", world.clockDeltas.size());
        summary.addProperty("answers", world.answers.size());
        summary.addProperty("orders", orders.size());
        summary.addProperty("checkedOrders", checkedOrders(rows));
        summary.addProperty("realizedOrders", realized.size());
        summary.addProperty("clockReadings", context - planted);
        summary.addProperty("fatalArms", rows.size() - context);
        summary.addProperty("placeholderPairings", placeholders);
        return summary;
    }

    private static int checkedOrders(List<JsonObject> edges) {
        int checked = 0;
        for (JsonObject edge : edges) {
            if (RecordingPlant.ORDER.equals(optionalString(edge, "kind"))
                    && RecordingPlant.checked(edge)) {
                checked++;
            }
        }
        return checked;
    }

    private static JsonObject assignedRoot(String rootId, String value,
                                           RootCategory category,
                                           World world, PlantSites sites) {
        OccurrenceAddress mint = mintOf(world, rootId);
        Set<String> marked = sites.sites(rootId);
        List<PlantSites.Call> calls = sites.calls(rootId);
        boolean planted = mint != null && (category == RootCategory.HOOK
                || category == RootCategory.FAULT && marked.size() == 1
                && ("true".equals(value) || "false".equals(value))
                || category == RootCategory.CONFIG && !calls.isEmpty()
                || category == RootCategory.READ && calls.size() == 1);
        if (!planted) {
            throw new Refused("NATIVE_PLANT_UNSUPPORTED: root " + rootId
                    + " is " + category + " at '" + value + "', minted at '"
                    + world.mints.get(rootId) + "' at " + sites.locations(
                    rootId) + ", called at " + marked + "; a native run "
                    + "plants a fault marker of one call site at true or "
                    + "false, a tree hook's field, or the return of a "
                    + "configuration getter or an accessor call, at an "
                    + "occurrence it is minted at");
        }
        JsonObject row = root(category, rootId, mint);
        if (category == RootCategory.FAULT) {
            row.addProperty(RecordingPlant.SITE, marked.iterator().next());
            row.addProperty(RecordingPlant.INVOCATION,
                    sites.invocation(rootId, mint));
        } else if (category == RootCategory.READ) {
            PlantSites.Call call = calls.get(0);
            row.addProperty(RecordingPlant.SITE, call.siteId);
            row.addProperty(RecordingPlant.CALLEE, call.callee);
            row.addProperty(RecordingPlant.JAVA_TYPE, call.javaType);
        } else if (category == RootCategory.CONFIG) {
            JsonArray getters = new JsonArray();
            for (PlantSites.Call call : calls) {
                getters.add(callRow(null, call));
            }
            row.add(RecordingPlant.SITES, getters);
            row.addProperty(RecordingPlant.JAVA_TYPE, calls.get(0).javaType);
        }
        row.addProperty(RecordingPlant.VALUE, value);
        return row;
    }

    private static JsonObject clockRoot(String rootId, String skew,
                                        World world, PlantSites sites) {
        OccurrenceAddress mint = mintOf(world, rootId);
        List<PlantSites.Call> calls = new ArrayList<PlantSites.Call>();
        for (PlantSites.Call call : sites.calls(rootId)) {
            if (call.clock != null) calls.add(call);
        }
        if (mint == null || calls.size() != 1 || !skew.matches("-?\\d+")) {
            throw new Refused("NATIVE_PLANT_UNSUPPORTED: clock " + rootId
                    + " skewed by '" + skew + "', minted at '"
                    + world.mints.get(rootId) + "', is read at "
                    + sites.locations(rootId) + " with " + calls.size()
                    + " declared clock call(s); a native run plants a skew "
                    + "of one clock call's return at an occurrence it is "
                    + "minted at");
        }
        JsonObject row = root(RootCategory.CLOCK, rootId, mint);
        for (Map.Entry<String, JsonElement> field
                : callRow(null, calls.get(0)).entrySet()) {
            row.add(field.getKey(), field.getValue());
        }
        row.addProperty(RecordingPlant.SKEW, skew);
        return row;
    }

    private static List<JsonObject> answers(Map<String, String> answers,
                                            Witness witness,
                                            PlantSites sites) {
        Map<String, Endpoint> attached = new LinkedHashMap<String, Endpoint>();
        for (SessionReader rows : Arrays.asList(witness.recording,
                witness.session)) {
            for (AttachRow attach : rows.attaches()) {
                attached.putIfAbsent(attach.endpoint().id(),
                        attach.endpoint());
            }
        }
        List<JsonObject> rows = new ArrayList<JsonObject>();
        for (Map.Entry<String, String> answer : answers.entrySet()) {
            Endpoint endpoint = attached.get(answer.getKey());
            String port = endpoint == null ? "" : endpoint.site();
            PlantSites.Capture capture = sites.capture(port);
            if (capture == null || !CommunicationCatalogContract
                    .CAPTURE_CALL_RETURN.equals(capture.kind)
                    || !capture.codecField.isEmpty()) {
                throw new Refused("NATIVE_PLANT_UNSUPPORTED: the world answers"
                        + " attach " + answer.getKey() + " of port '" + port
                        + "', captured " + (capture == null ? "nowhere"
                        : capture.kind + (capture.codecField.isEmpty() ? ""
                        : " of message field " + capture.codecField))
                        + "; a native run answers a value a call returns, "
                        + "not a parameter, an argument, a method's return "
                        + "or a message getter's element (which getter call "
                        + "attaches is the decode's binding, kept only in a "
                        + "replay)");
            }
            JsonObject row = new JsonObject();
            row.addProperty(RecordingPlant.KIND, RecordingPlant.ANSWER);
            row.addProperty(RecordingPlant.ENDPOINT, answer.getKey());
            row.addProperty(RecordingPlant.PORT, port);
            row.addProperty(RecordingPlant.SITE, capture.siteId);
            row.addProperty(RecordingPlant.CALLEE, capture.callee);
            row.add(RecordingPlant.REGIONS, textArray(capture.regions));
            row.addProperty(RecordingPlant.VALUE, answer.getValue());
            rows.add(row);
        }
        return rows;
    }

    private static OccurrenceAddress mintOf(World world, String rootId) {
        String rendered = world.mints.getOrDefault(rootId, "");
        try {
            return rendered.isEmpty() ? null
                    : OccurrenceAddress.parse(rendered);
        } catch (IllegalArgumentException notAnOccurrence) {
            return null;
        }
    }

    private static JsonObject root(RootCategory category, String rootId,
                                   OccurrenceAddress mint) {
        JsonObject row = new JsonObject();
        row.addProperty(RecordingPlant.KIND, RecordingPlant.ROOT);
        row.addProperty(RecordingPlant.CATEGORY, category.name());
        row.addProperty(RecordingPlant.ROOT_ID, rootId);
        row.addProperty(RecordingPlant.OCCURRENCE, mint.id());
        return row;
    }

    private static JsonObject callRow(String kind, PlantSites.Call call) {
        JsonObject row = new JsonObject();
        if (kind != null) row.addProperty(RecordingPlant.KIND, kind);
        row.addProperty(RecordingPlant.SITE, call.siteId);
        row.addProperty(RecordingPlant.CALLEE, call.callee);
        row.addProperty(RecordingPlant.JAVA_TYPE, call.javaType);
        if (call.clock != null) {
            JsonObject clock = new JsonObject();
            clock.addProperty(RecordingPlant.NANOS, call.clock.nanos());
            clock.addProperty(RecordingPlant.SOURCE, call.clock.source());
            row.add(RecordingPlant.CLOCK, clock);
        }
        return row;
    }

    private static JsonArray textArray(Iterable<String> texts) {
        JsonArray array = new JsonArray();
        for (String text : texts) array.add(text);
        return array;
    }

    private static Moved moved(JsonObject decided, JsonObject manifest,
                               SessionReader session,
                               SessionReader recording) {
        Map<String, String> readings = new LinkedHashMap<String, String>();
        for (JsonElement element : array(manifest, "roots")) {
            JsonObject root = element.getAsJsonObject();
            if ("CLOCK".equals(optionalString(root, "kind"))) {
                readings.put(optionalString(root, "rootId"),
                        optionalString(root, "recordedValue"));
            }
        }
        return Moved.of(ExploreCodec.map(object(decided, "movedRoots")),
                readings, session, recording);
    }

    static JsonObject decide(Path claimFile, Path worker, Path sessions)
            throws IOException {
        JsonObject decided = decision(claimFile, worker, sessions);
        Path edges = worker.resolve(Confirmation.FILE);
        int checked = Files.isReadable(edges)
                ? checkedOrders(RowCodec.readJsonl(edges)) : 0;
        if (checked == 0) return decided;
        int observed = 0;
        String sessionId = optionalString(decided, "sessionId");
        Path gaps = sessionId.isEmpty() ? null
                : sessions.resolve(sessionId).resolve(SessionDir.GAPS);
        if (gaps != null && Files.isReadable(gaps)) {
            for (JsonObject gap : RowCodec.readJsonl(gaps)) {
                if (GapKind.ORDER_OBSERVED.name().equals(
                        optionalString(gap, "kind"))) {
                    observed++;
                }
            }
        }
        decided.addProperty("ordersChecked", checked);
        decided.addProperty("ordersObserved", observed);
        return decided;
    }

    private static JsonObject decision(Path claimFile, Path worker,
                                       Path sessions) throws IOException {
        List<JsonObject> results =
                RowCodec.readJsonl(worker.resolve(ObligationDir.RESULT));
        JsonObject result = results.isEmpty() ? new JsonObject()
                : results.get(0);
        String verdict = optionalString(result, "verdict");
        String sessionId = optionalString(result, "sessionId");
        if (!"ADMITTED".equals(verdict)) {
            return confirmation(false, true, "the confirmation replay was "
                    + (verdict.isEmpty() ? "not run" : verdict) + ": "
                    + optionalString(result, "detail"), sessionId);
        }
        Path session = sessions.resolve(sessionId);
        if (sessionId.isEmpty() || !Files.isDirectory(session)) {
            return confirmation(false, true, "the confirmation replay names "
                    + "session " + sessionId + ", which " + sessions
                    + " does not hold", sessionId);
        }
        List<JsonObject> gaps;
        List<TargetRow> targets;
        try {
            gaps = published(session.resolve(SessionDir.GAPS));
            targets = new ArrayList<TargetRow>();
            for (JsonObject row
                    : published(session.resolve(SessionDir.TARGETS))) {
                targets.add(RowCodec.readTarget(row));
            }
        } catch (IOException | RuntimeException unread) {
            return confirmation(false, true, "the run's session could not be"
                    + " read, so it answers nothing: " + unread.getMessage(),
                    sessionId);
        }
        for (JsonObject gap : gaps) {
            if ("CONFIRM_MISMATCH".equals(optionalString(gap, "kind"))) {
                return confirmation(false, true, "the run took an edge the"
                        + " model did not choose, so it did not run the"
                        + " model: " + optionalString(gap, "detail"),
                        sessionId);
            }
        }
        JsonObject claim;
        OccurrenceAddress anchor;
        try {
            claim = ExploreCodec.readObject(claimFile);
            anchor = OccurrenceAddress.parse(optionalString(claim, "anchor"));
        } catch (RuntimeException unparsed) {
            return confirmation(false, false, "the claim states no parseable"
                    + " anchor: " + unparsed.getMessage(), sessionId);
        }
        int elsewhere = 0;
        for (TargetRow target : targets) {
            if (!target.reachedAnchor() || !target.observedFatal()) continue;
            if (target.occurrence().id().equals(anchor.id())) {
                return confirmation(true, false, "every edge the model chose"
                        + " was taken, and the claim's anchor observed the"
                        + " fatal", sessionId);
            }
            elsewhere++;
        }
        String why = "the run published no target row at the claim's"
                + " anchor " + anchor.id() + " that reached it and observed"
                + " the fatal" + (elsewhere == 0 ? ""
                : " (" + elsewhere + " row(s) at other occurrences did)");
        String unplanted;
        try {
            unplanted = unplanted(claim, gaps, published(session.resolve(
                    SessionDir.ROOTS)));
        } catch (IOException | RuntimeException unread) {
            unplanted = "its root rows could not be read: "
                    + unread.getMessage();
        }
        return confirmation(false, true, unplanted.isEmpty() ? why
                : why + ", and " + unplanted, sessionId);
    }

    static String unplanted(JsonObject claim, List<JsonObject> gaps,
                            List<JsonObject> roots) {
        for (JsonObject gap : gaps) {
            if ("ASSIGNMENT_UNPLANTED".equals(optionalString(gap, "kind"))) {
                return "it refused a plant (" + optionalString(gap,
                        "subject") + ")";
            }
        }
        Map<String, RootMintRow> minted =
                new LinkedHashMap<String, RootMintRow>();
        for (JsonObject row : roots) {
            RootMintRow root = RowCodec.readRootMint(row);
            minted.putIfAbsent(root.rootId(), root);
            minted.putIfAbsent(root.symbol(), root);
        }
        for (Map.Entry<String, JsonElement> moved : object(claim.getAsJsonObject(
                "claim"), "movedRoots").entrySet()) {
            RootMintRow root = minted.get(moved.getKey());
            if (root == null) {
                return "it minted no row of the moved root "
                        + moved.getKey();
            }
            String model = moved.getValue().getAsString().trim();
            if (root.kind() != RootKind.CLOCK && !root.recordedValue().trim()
                    .equalsIgnoreCase(model)) {
                return "it ran the moved root " + moved.getKey() + " at "
                        + root.recordedValue() + ", not the model's " + model;
            }
        }
        return "";
    }

    private static List<JsonObject> published(Path file) throws IOException {
        if (!Files.isReadable(file)) {
            throw new IOException("it published no readable " + file);
        }
        return RowCodec.readJsonl(file);
    }

    private static JsonObject confirmation(boolean confirmed, boolean refutes,
                                           String reason, String sessionId) {
        JsonObject confirmation = new JsonObject();
        confirmation.addProperty("schemaVersion", 1);
        confirmation.addProperty("kind", "CONFIRMATION");
        confirmation.addProperty("confirmed", confirmed);
        confirmation.addProperty("refutes", refutes);
        confirmation.addProperty("reason", reason);
        confirmation.addProperty("sessionId", sessionId);
        return confirmation;
    }

    private static JsonObject summary(OccurrenceAddress anchor, String pathId,
                                      String sessionId, int ordinal) {
        JsonObject summary = new JsonObject();
        summary.addProperty("kind", "CONFIRM_TASK");
        summary.addProperty("anchor", anchor.id());
        summary.addProperty("selectedPathId", pathId);
        summary.addProperty("selectedSessionId", sessionId);
        summary.addProperty("valuationOrdinal", ordinal);
        return summary;
    }

    static String realizedBy(Moved moved, JsonObject world, String sessionId,
                             List<JsonObject> arms, SessionReader session,
                             OccurrenceAddress anchor, boolean sawChosen) {
        boolean fatal = false;
        for (TargetRow row : session.targets()) {
            fatal |= row.occurrence().id().equals(anchor.id())
                    && row.reachedAnchor() && row.observedFatal();
        }
        if (!fatal || !sawChosen || !ownDeliveries(sessionId, arms)
                || !moved.ranBy(ExploreCodec.readWorld(world), session)) {
            return "";
        }
        int count = moved.count();
        return "the selected session " + sessionId + " is itself the run: "
                + "it took every edge the model chose (" + arms.size()
                + " arm(s), all its own deliveries), ran "
                + (count == 0 ? "no moved root"
                : "every moved root at the model's value")
                + ", and observed the fatal at the anchor";
    }

    private static boolean ownDeliveries(String sessionId,
                                         List<JsonObject> arms) {
        for (JsonObject arm : arms) {
            if (!sessionId.equals(optionalString(arm, "sessionId"))) {
                return false;
            }
        }
        return true;
    }

    static JsonObject obligationWorld(Path iteration, String sessionId)
            throws IOException {
        JsonObject world = ObligationDir.worlds(
                ObligationDir.workersIn(iteration)).get(sessionId);
        return world == null ? new JsonObject() : world;
    }

    private static List<JsonObject> markerEdges(
            JsonObject manifest, Map<String, String> assignments) {
        List<JsonObject> markers = new ArrayList<JsonObject>();
        for (JsonElement element : array(manifest, "roots")) {
            JsonObject root = element.getAsJsonObject();
            String rootId = optionalString(root, "rootId");
            if (!"MARKER".equals(optionalString(root, "kind"))
                    || !assignments.containsKey(rootId)) {
                continue;
            }
            JsonObject marker = new JsonObject();
            marker.addProperty("kind", "MARKER");
            marker.addProperty("root", rootId);
            marker.addProperty("value",
                    Boolean.parseBoolean(assignments.get(rootId)));
            markers.add(marker);
        }
        return markers;
    }

    private static List<JsonObject> wireEdges(
            List<JsonObject> arms, Map<String, SessionReader> armSessions,
            OccurrenceAddress anchor, Set<OccurrenceAddress> cone)
            throws IOException {
        List<JsonObject> edges = new ArrayList<JsonObject>();
        for (JsonObject arm : arms) {
            String selector = optionalString(arm, "selector");
            if (!selector.startsWith("message_arm__")) continue;
            SessionReader producerSession =
                    armSessions.get(optionalString(arm, "sessionId"));
            if (producerSession == null) continue;
            for (JsonElement consumer : array(arm, "attachEndpointIds")) {
                String consumerId = consumer.getAsString();
                AttachRow paired = null;
                for (AttachRow row : producerSession.attaches()) {
                    if (row.endpoint().id().equals(consumerId)) paired = row;
                }
                if (paired == null || paired.producer() == null) {
                    throw new Refused("selected arm " + selector
                            + " names consumer " + consumerId + ", which "
                            + "session " + optionalString(arm, "sessionId")
                            + " states no paired attach for");
                }
                JsonObject edge = new JsonObject();
                edge.addProperty("kind", "WIRE");
                edge.addProperty("consumer",
                        Confirmation.id(paired.endpoint()));
                edge.addProperty("producer",
                        Confirmation.id(paired.producer()));
                edge.addProperty("selector", selector);
                cone.add(paired.endpoint().occurrence());
                cone.add(paired.producer().occurrence());
                if (paired.endpoint().occurrence().id().equals(anchor.id())
                        && producerSession.answered().contains(
                        anchor.render())) {
                    edge.add(Confirmation.PRODUCER_QUESTION,
                            question(paired.producer(), producerSession));
                }
                JsonObject texts = object(arm, ComposeMain.TEXTS);
                if (texts.has(consumerId)) {
                    edge.add("value", named(texts.get(consumerId),
                            producerSession.manifest()));
                }
                edges.add(edge);
            }
        }
        return edges;
    }

    static JsonElement named(JsonElement text, SessionManifest manifest) {
        if (manifest == null || !text.isJsonPrimitive()) return text;
        String raw = text.getAsString();
        String named = manifest.runSpellings().name(raw);
        return named.equals(raw) ? text : new JsonPrimitive(named);
    }

    private static JsonObject question(Endpoint producer,
                                       SessionReader session)
            throws IOException {
        Map<String, ContextShape.Stance> senders =
                new LinkedHashMap<String, ContextShape.Stance>();
        for (ScheduleEvent event : session.schedule()) {
            if (event.kind() != ScheduleEvent.Kind.SEND
                    || event.endpoint().isEmpty()) {
                continue;
            }
            ContextShape.Stance stance =
                    ContextShape.Stance.ofSend(event.context());
            if (stance != null) senders.put(event.endpoint(), stance);
        }
        JsonObject question = new JsonObject();
        question.addProperty("occurrence", producer.occurrence().render());
        question.addProperty("site", producer.site());
        question.addProperty("siteIndex", producer.siteIndex().hash());
        question.addProperty("attempt", producer.attempt());
        JsonArray shape = new JsonArray();
        for (String hop : ContextShape.of(producer.occurrence().context(),
                senders::get)) {
            shape.add(hop);
        }
        question.add("shape", shape);
        return question;
    }

    private static final class StateClosure {
        private final Map<String, WriteRow> writes =
                new LinkedHashMap<String, WriteRow>();
        private final Map<String, List<WriteRow>> byLocation =
                new LinkedHashMap<String, List<WriteRow>>();
        private final Map<String, ReadRow> readers =
                new LinkedHashMap<String, ReadRow>();
        private final List<ReadRow> reads = new ArrayList<ReadRow>();
        private final Map<String, WriteRow> joined =
                new LinkedHashMap<String, WriteRow>();
        private final Set<String> past = new LinkedHashSet<String>();
        private final Map<String, ActivationRow> activations =
                new LinkedHashMap<String, ActivationRow>();
        private final Set<String> servingTasks;
        private final Map<String, List<Placed>> placed =
                new LinkedHashMap<String, List<Placed>>();
        private final Map<String, Long> last = new HashMap<String, Long>();

        private static final class Placed {
            private final List<Frame> frames;
            private final long seq;

            private Placed(Endpoint at, long seq) {
                this.frames = at.activationFrames();
                this.seq = seq;
            }
        }

        private void place(Endpoint at, long seq) {
            if (at == null) return;
            placed.computeIfAbsent(at.occurrence().id(),
                    key -> new ArrayList<Placed>()).add(new Placed(at, seq));
            last(at.occurrence(), seq);
        }

        private void last(OccurrenceAddress occurrence, long seq) {
            last.merge(occurrence.id(), seq, Math::max);
        }

        private Exit closing(OccurrenceAddress occurrence) {
            return new Exit(occurrence, Collections.<Frame>emptyList(),
                    last.get(occurrence.id()));
        }

        private String order(Holding holding, Exit first, Endpoint then,
                             long thenSeq) {
            if (first.occurrence.id().equals(then.occurrence().id())) {
                return null;
            }
            Hold hold = held(first, then, thenSeq);
            String order = first.activation + "\n" + hold.activation;
            holding.orders.add(order);
            if (hold.checked) holding.checked.add(order);
            holding.cone.add(first.occurrence);
            holding.cone.add(hold.occurrence);
            if (thenSeq < first.seq) {
                holding.reordered.add(hold.occurrence.id());
            }
            return order;
        }

        private static final class Exit {
            private final String activation;
            private final OccurrenceAddress occurrence;
            private final long seq;

            private Exit(OccurrenceAddress occurrence, List<Frame> frames,
                         long seq) {
                this.activation = Confirmation.activation(occurrence,
                        ExecutionIndex.of(frames));
                this.occurrence = occurrence;
                this.seq = seq;
            }
        }

        private Exit exit(Endpoint event, long seq) {
            return outermost(event) ? closing(event.occurrence())
                    : new Exit(event.occurrence(), event.activationFrames(),
                    seq);
        }

        private boolean outermost(Endpoint event) {
            int depth = event.activationFrames().size();
            List<Placed> events = placed.get(event.occurrence().id());
            for (Placed other : events == null
                    ? Collections.<Placed>emptyList() : events) {
                if (other.frames.size() < depth) return false;
            }
            return true;
        }

        private static final class Hold {
            private final OccurrenceAddress occurrence;
            private final String activation;
            private final boolean checked;

            private Hold(OccurrenceAddress occurrence, List<Frame> frames,
                         boolean checked) {
                this.occurrence = occurrence;
                this.activation = Confirmation.activation(occurrence,
                        ExecutionIndex.of(frames));
                this.checked = checked;
            }
        }

        private Hold held(Exit first, Endpoint event, long seq) {
            Endpoint send;
            try {
                send = Confirmation.submitter(event.occurrence(),
                        activations::get, servingTasks);
            } catch (IllegalStateException unheld) {
                return holdBefore(event, seq, true);
            }
            if (send == null) return holdBefore(event, seq, false);
            if (Confirmation.standsUnder(first.occurrence, send,
                    activations::get)) {
                return holdBefore(event, seq, true);
            }
            return new Hold(send.occurrence(), send.activationFrames(),
                    false);
        }

        private Hold holdBefore(Endpoint event, long seq, boolean checked) {
            List<Frame> own = event.activationFrames();
            List<Frame> hold = own;
            long latest = Long.MIN_VALUE;
            List<Placed> events = placed.get(event.occurrence().id());
            for (Placed other : events == null
                    ? Collections.<Placed>emptyList() : events) {
                if (other.seq >= seq || other.seq <= latest
                        || other.frames.size() <= own.size()
                        || !other.frames.subList(0, own.size()).equals(own)) {
                    continue;
                }
                latest = other.seq;
                hold = other.frames.subList(0, own.size() + 1);
            }
            if (hold == own && outermost(event)) {
                hold = Collections.<Frame>emptyList();
            }
            return new Hold(event.occurrence(), hold, checked);
        }

        private StateClosure(SessionReader session) {
            servingTasks = session.manifest() == null
                    ? Collections.<String>emptySet()
                    : session.manifest().servingTasks();
            for (ActivationRow activation : session.activations()) {
                activations.putIfAbsent(activation.occurrence().id(),
                        activation);
            }
            for (ReadRow read : session.reads()) {
                place(read.endpoint(), read.seq());
                reads.add(read);
            }
            for (ExportRow export : session.exports()) {
                place(export.endpoint(), export.seq());
            }
            for (AttachRow attach : session.attaches()) {
                place(attach.endpoint(), attach.seq());
            }
            for (DecisionRow decision : session.decisions()) {
                last(decision.occurrence(), decision.seq());
            }
            for (WriteRow write : session.writes()) {
                if (!write.initial()) place(write.endpoint(), write.seq());
                writes.put(version(write.location(), write.version()), write);
                byLocation.computeIfAbsent(SmtLowering.locationKey(
                        write.location()),
                        key -> new ArrayList<WriteRow>()).add(write);
            }
        }

        private StateClosure(SessionReader session, OccurrenceAddress anchor,
                             long cutoff) {
            this(session);
            Map<String, List<ReadRow>> readsOn =
                    new LinkedHashMap<String, List<ReadRow>>();
            for (ReadRow read : session.reads()) {
                readsOn.computeIfAbsent(read.endpoint().occurrence().id(),
                        key -> new ArrayList<ReadRow>()).add(read);
            }
            RestsOn.closure(new RestsOn.Log() {
                @Override
                public List<ReadRow> readsOn(String occurrenceId) {
                    return readsOn.getOrDefault(occurrenceId,
                            Collections.<ReadRow>emptyList());
                }

                @Override
                public WriteRow writeOf(String locationKey, long version) {
                    return writes.get(locationKey + "@" + version);
                }

                @Override
                public List<WriteRow> writesOf(String locationKey) {
                    return byLocation.getOrDefault(locationKey,
                            Collections.<WriteRow>emptyList());
                }
            }, anchor, anchor, cutoff, null, false, new RestsOn.Reads() {
                @Override
                public void joined(ReadRow read, WriteRow write) {
                    readers.put(read.endpoint().id(), read);
                    if (write != null) joined.put(read.endpoint().id(), write);
                }

                @Override
                public void past(ReadRow read) {
                    past.add(read.endpoint().id());
                }
            });
        }

        private Map<String, WriteRow> chosen(List<JsonObject> arms) {
            Map<String, WriteRow> chosen = new LinkedHashMap<String, WriteRow>();
            for (JsonObject arm : arms) {
                String selector = optionalString(arm, "selector");
                if (!selector.startsWith("writer_arm__")) continue;
                Set<String> fills = new LinkedHashSet<String>(
                        strings(arm, "interactionIds"));
                Map<String, WriteRow> byVersion =
                        new LinkedHashMap<String, WriteRow>();
                for (ReadRow read : reads) {
                    WriteRow held = filled(fills, read);
                    if (held != null) {
                        byVersion.merge(SmtLowering.locationKey(
                                read.location()) + "@"
                                + read.observedVersion(), held,
                                (one, other) -> RowOrder.compare(other, one)
                                        > 0 ? other : one);
                    }
                }
                for (ReadRow read : readers.values()) {
                    WriteRow held = filled(fills, read);
                    if (held == null) {
                        held = byVersion.get(SmtLowering.locationKey(
                                read.location()) + "@"
                                + read.observedVersion());
                    }
                    if (held != null) chosen.put(read.endpoint().id(), held);
                }
                for (JsonElement element : array(arm, "referentStates")) {
                    JsonObject state = element.getAsJsonObject();
                    String reader = optionalString(state, "reader");
                    String seen = optionalString(state, "location") + "@"
                            + optionalString(state, "version");
                    WriteRow write = writes.get(seen);
                    String subject = "selected arm " + selector
                            + " answers a query through a re-pointable "
                            + "reference from state " + seen + " ("
                            + optionalString(state, "selector") + ")";
                    if (reader.isEmpty()) {
                        throw new Refused(subject + ", asked outside every "
                                + "read of a container, so no read of the "
                                + "run can be held to it");
                    }
                    if (!readers.containsKey(reader)) {
                        if (past.contains(reader)) continue;
                        throw new Refused(subject + " at read " + reader
                                + ", which is no read of the anchor's join "
                                + "closure");
                    }
                    if (write == null || !write.endpoint().id().equals(
                            optionalString(state, "writer"))) {
                        throw new Refused(subject + ", which the selected "
                                + "session states no write of by "
                                + optionalString(state, "writer"));
                    }
                    chosen.put(reader, write);
                }
            }
            return chosen;
        }

        private WriteRow filled(Set<String> fills, ReadRow read) {
            WriteRow held = null;
            for (WriteRow write : byLocation.getOrDefault(
                    SmtLowering.locationKey(read.location()),
                    Collections.<WriteRow>emptyList())) {
                if (!fills.contains(Interaction.of(InteractionKind.STATE,
                        write.endpoint(), read.endpoint()).id())
                        || held != null && held.version()
                        == read.observedVersion()) {
                    continue;
                }
                if (held == null || write.version() == read.observedVersion()
                        || RowOrder.compare(write, held) > 0) {
                    held = write;
                }
            }
            return held;
        }

        private boolean ran(Map<String, WriteRow> chosen) {
            for (Map.Entry<String, WriteRow> each : chosen.entrySet()) {
                if (!each.getValue().equals(joined.get(each.getKey()))) {
                    return false;
                }
            }
            return true;
        }
    }

    static final class Holding {
        final List<JsonObject> edges = new ArrayList<JsonObject>();
        final Set<String> reordered = new LinkedHashSet<String>();
        long cutBefore = Long.MAX_VALUE;
        final Set<OccurrenceAddress> cone =
                new LinkedHashSet<OccurrenceAddress>();
        private final Set<String> orders = new LinkedHashSet<String>();
        private final Set<String> checked = new LinkedHashSet<String>();
        private final Set<String> chosenOrders = new LinkedHashSet<String>();

        private void order(String order, boolean chosen) {
            if (order != null && chosen) chosenOrders.add(order);
        }

        Set<String> history() {
            Set<String> history = new LinkedHashSet<String>(orders);
            history.removeAll(chosenOrders);
            return history;
        }
    }

    private static Holding stateEdges(StateClosure closure,
                                      List<ReadRow> reads,
                                      Map<String, WriteRow> chosen,
                                      Set<String> chosenAt,
                                      boolean block) {
        Holding holding = new Holding();
        for (ReadRow read : reads) {
            StateClosure.Exit reading = block
                    ? closure.closing(read.endpoint().occurrence())
                    : closure.exit(read.endpoint(), read.seq());
            String reader = read.endpoint().id();
            WriteRow held = chosen.containsKey(reader) ? chosen.get(reader)
                    : closure.joined.get(reader);
            if (held == null || !chosen.containsKey(reader)
                    && held.initial()) {
                continue;
            }
            String location = SmtLowering.locationKey(held.location());
            boolean mint = read.mintVersion() != ReadRow.UNKNOWN_VERSION;
            JsonObject edge = new JsonObject();
            edge.addProperty("kind", "STATE");
            edge.addProperty("reader", Confirmation.id(read.endpoint()));
            if (read.location().kind() != LocationKind.VIEW) {
                edge.addProperty("readerAnyTurn",
                        Confirmation.anyTurn(read.endpoint()));
            }
            edge.addProperty("mint", mint);
            edge.addProperty("writer", Confirmation.writer(held));
            edge.addProperty("version", held.version());
            edge.addProperty("location", location);
            holding.edges.add(edge);
            holding.cone.add(read.endpoint().occurrence());
            if (!held.initial()) {
                holding.cone.add(held.endpoint().occurrence());
            }
            if (mint || held.location().kind() == LocationKind.STORE) continue;
            if (held.location().kind() == LocationKind.VIEW) {
                if (!Confirmation.hookPublishes(held.location())) {
                    if (held.location().equals(read.location())
                            && held.version() == read.observedVersion()) {
                        continue;
                    }
                    throw new Refused("PAIRING_UNHELD: read " + reader
                            + " of " + held.location() + " is held to"
                            + " version " + held.version() + ", not the "
                            + read.observedVersion() + " it observed, and"
                            + " no publication hook publishes the view (no"
                            + " PUBLISHED_VIEW of it), so no hold can defer"
                            + " it");
                }
                JsonObject hold = new JsonObject();
                hold.addProperty("kind", RecordingPlant.VIEW_HOLD);
                hold.addProperty("view",
                        Confirmation.viewKey(held.location()));
                hold.addProperty("above", held.version());
                OccurrenceAddress readBy = read.endpoint().occurrence();
                hold.addProperty("readerContext",
                        Confirmation.contextKey(readBy));
                hold.addProperty("reader", Confirmation.id(read.endpoint()));
                hold.addProperty("until", readBy.role() ? ""
                        : Confirmation.activation(readBy,
                        ExecutionIndex.empty()));
                holding.edges.add(hold);
                for (WriteRow decode : closure.byLocation.getOrDefault(
                        location, Collections.<WriteRow>emptyList())) {
                    if (decode.version() <= held.version()
                            || decode.initial()) {
                        continue;
                    }
                    holding.cone.add(decode.endpoint().occurrence());
                    if (RowOrder.before(decode, read)) {
                        holding.cutBefore = Math.min(holding.cutBefore,
                                decode.seq());
                    }
                }
                continue;
            }
            boolean model = chosen.containsKey(reader)
                    || chosenAt.contains(location);
            if (!held.initial()) {
                holding.order(closure.order(holding, closure.exit(
                        held.endpoint(), held.seq()), read.endpoint(),
                        read.seq()), model);
            }
            for (WriteRow other : closure.byLocation.get(location)) {
                if (other.endpoint().equals(held.endpoint())
                        || other.initial()) {
                    continue;
                }
                if (!held.initial() && RowOrder.compare(other, held) < 0) {
                    holding.order(closure.order(holding, closure.exit(
                            other.endpoint(), other.seq()), held.endpoint(),
                            held.seq()), model);
                } else {
                    holding.order(closure.order(holding, reading,
                            other.endpoint(), other.seq()), model);
                }
            }
        }
        for (String order : holding.orders) {
            String[] ends = order.split("\n", 2);
            JsonObject row = new JsonObject();
            row.addProperty("kind", "ORDER");
            row.addProperty("before", ends[0]);
            row.addProperty("after", ends[1]);
            if (holding.checked.contains(order)) {
                row.addProperty(RecordingPlant.CHECK, true);
            }
            holding.edges.add(row);
        }
        return holding;
    }

    private static void heldOnce(List<JsonObject> edges) {
        Map<String, String> writers = new LinkedHashMap<String, String>();
        for (JsonObject edge : edges) {
            if (!"STATE".equals(optionalString(edge, "kind"))) continue;
            String reader = optionalString(edge, "reader");
            String writer = optionalString(edge, "writer");
            String held = writers.put(reader, writer);
            if (held != null && !held.equals(writer)) {
                throw new Refused("STATE_CONFLICT: read " + reader
                        + " is held to writers " + held + " and " + writer
                        + ": the model's choice and the selected session's"
                        + " world disagree");
            }
        }
    }


    static Holding holding(SessionReader session,
                           Map<String, String> pairings) {
        StateClosure closure = new StateClosure(session);
        List<ReadRow> reads = new ArrayList<ReadRow>();
        Map<String, WriteRow> chosen = new LinkedHashMap<String, WriteRow>();
        Set<String> found = new LinkedHashSet<String>();
        for (ReadRow read : session.reads()) {
            String reader = Confirmation.id(read.endpoint());
            String writer = pairings.get(reader);
            if (writer == null) continue;
            WriteRow held = null;
            for (WriteRow write : closure.byLocation.getOrDefault(
                    SmtLowering.locationKey(read.location()),
                    Collections.<WriteRow>emptyList())) {
                if (!writer.equals(Confirmation.writer(write))
                        || held != null && held.version()
                        == read.observedVersion()) {
                    continue;
                }
                if (held == null || write.version() == read.observedVersion()
                        || RowOrder.compare(write, held) > 0) {
                    held = write;
                }
            }
            if (held == null) {
                throw new Refused("PAIRING_UNSTATED: the world pairs read "
                        + reader + " with writer " + writer + ", which "
                        + "session " + session.sessionId() + " states no "
                        + "write of " + read.location() + " by");
            }
            found.add(reader);
            reads.add(read);
            chosen.put(read.endpoint().id(), held);
        }
        Set<String> unread = new LinkedHashSet<String>(pairings.keySet());
        unread.removeAll(found);
        if (!unread.isEmpty()) {
            throw new Refused("PAIRING_UNSTATED: the world pairs read(s) "
                    + unread + ", which session " + session.sessionId()
                    + " states no read at");
        }
        return stateEdges(closure, reads, chosen,
                Collections.<String>emptySet(), true);
    }

    private static String version(LocationId location, long version) {
        return SmtLowering.locationKey(location) + "@" + version;
    }

    private static JsonObject valuation(JsonObject claim, int ordinal) {
        for (JsonElement element : array(claim, "valuations")) {
            JsonObject row = element.getAsJsonObject();
            if (row.get("ordinal").getAsInt() == ordinal) return row;
        }
        throw new Refused("the claim rests on valuation " + ordinal
                + ", which it does not state");
    }

}
