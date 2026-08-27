package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

/**
 * The Step 2 shared-map contracts, checked against real emitted artifacts.
 *
 * <p>Four claims are pinned here, and each is the acceptance criterion of one
 * half of the step:</p>
 *
 * <ul>
 *   <li>a {@code MAP_STATE} record is admitted, sliced and lowered by exactly
 *   the code a scalar field record is;</li>
 *   <li>two writers that installed <em>equal</em> map states stay two arms of
 *   the choice, because concrete equality is not provenance;</li>
 *   <li>selecting a different arm changes the reader's own value equality and
 *   its read cut together, so the selector is not order-only metadata;</li>
 *   <li>an unsupported mutation, a writer no arm carries, and an occurrence
 *   axis nothing declared each produce their own named gap.</li>
 * </ul>
 *
 * <p>Every formula assertion below reads the composer's own output. Nothing
 * inspects an emitter internal, so a refactor that keeps the contract keeps
 * the test.</p>
 */
public class RecordedMapStateTest {

    @Rule
    public final TemporaryFolder temporary = new TemporaryFolder();

    private static final String EVENT = String.valueOf(
            RecordedMapStateFixtures.QUERY_EVENT);
    private static final String RF1 =
            RecordedSessionModel.selectorNameToken(EVENT, "rf1");
    private static final String RF2 =
            RecordedSessionModel.selectorNameToken(EVENT, "rf2");
    private static final String RF_UNKNOWN =
            RecordedSessionModel.selectorNameToken(EVENT,
                    SharedStateEvidence.UNKNOWN_WRITER_SELECTOR);

    @Test
    public void boundedMapPortStillDeclaresSharedCarrier() {
        JsonObject port = new JsonObject();
        port.addProperty("javaType", "java.util.Map");
        port.addProperty("rootKind", "RECEIVER");
        port.addProperty("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        JsonArray path = new JsonArray();
        path.add("state");
        path.add("allKeys");
        port.add("fieldPath", path);
        JsonArray declarations = new JsonArray();
        declarations.add("<example.NameNode: example.State state>");
        declarations.add("<example.State: java.util.Map allKeys>");
        port.add("fieldPathDeclarations", declarations);

        Map<String, JsonObject> carriers = new LinkedHashMap<>();
        ConcolicScheduler.declareMapStateCarrier(carriers, port);

        assertEquals(1, carriers.size());
        JsonObject carrier = carriers.values().iterator().next();
        assertEquals(SharedStateEvidence.LOCATION_KIND_MAP_STATE,
                string(carrier, "kind"));
        assertEquals("example.State", string(carrier, "declaringClass"));
        assertEquals("allKeys", string(carrier, "fieldName"));
        assertEquals("Ljava/util/Map;", string(carrier, "descriptor"));
        assertEquals(path, array(carrier, "fieldPath"));
    }

    @Test
    public void observedMapAccessDeclaresItsExactAccessOwnerCarrier() {
        JsonObject port = new JsonObject();
        port.addProperty("javaType", "java.util.Map");
        port.addProperty("rootKind", "OBSERVED_FIELD_RECEIVER");
        port.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
        port.addProperty("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        JsonArray path = new JsonArray();
        path.add("allKeys");
        port.add("fieldPath", path);
        JsonArray declarations = new JsonArray();
        declarations.add("<example.SecretManager: java.util.Map allKeys>");
        port.add("fieldPathDeclarations", declarations);

        Map<String, JsonObject> carriers = new LinkedHashMap<>();
        ConcolicScheduler.declareMapStateCarrier(carriers, port);

        assertEquals(1, carriers.size());
        JsonObject carrier = carriers.values().iterator().next();
        assertEquals(SharedStateEvidence.LOCATION_KIND_MAP_STATE,
                string(carrier, "kind"));
        assertEquals("example.SecretManager",
                string(carrier, "declaringClass"));
        assertEquals("allKeys", string(carrier, "fieldName"));
        assertEquals("Ljava/util/Map;", string(carrier, "descriptor"));
        assertEquals("ACTIVATION_FIELD_RECEIVER",
                string(carrier, "sourceKind"));
        assertTrue(array(carrier, "fieldPath").isEmpty());
    }

    @Test
    public void selectedMapReadFromDeclaresBothExactAccessOwners() {
        JsonObject edge = new JsonObject();
        edge.addProperty("fromOccurrenceId", "occ.writer");
        edge.addProperty("toOccurrenceId", "occ.reader");
        edge.addProperty(RecordedReadFrom.EDGE_FIELD,
                "example.SecretManager#allKeys");
        JsonArray declarations = new JsonArray();
        declarations.add("<example.SecretManager: java.util.Map allKeys>");
        edge.add("fieldPathDeclarations", declarations);
        JsonArray edges = new JsonArray();
        edges.add(edge);

        JsonObject writer = new JsonObject();
        JsonObject reader = new JsonObject();
        JsonObject unrelated = new JsonObject();
        ConcolicScheduler.declareReadFromCarriers(writer, edges,
                "occ.writer");
        ConcolicScheduler.declareReadFromCarriers(reader, edges,
                "occ.reader");
        ConcolicScheduler.declareReadFromCarriers(unrelated, edges,
                "occ.other");

        for (JsonObject task : Arrays.asList(writer, reader)) {
            assertEquals(1, array(task, "sharedCarriers").size());
            JsonObject carrier = array(task, "sharedCarriers")
                    .get(0).getAsJsonObject();
            assertEquals(SharedStateEvidence.LOCATION_KIND_MAP_STATE,
                    string(carrier, "kind"));
            assertEquals("example.SecretManager",
                    string(carrier, "declaringClass"));
            assertEquals("allKeys", string(carrier, "fieldName"));
            assertEquals("Ljava/util/Map;",
                    string(carrier, "descriptor"));
            assertEquals("ACTIVATION_FIELD_RECEIVER",
                    string(carrier, "sourceKind"));
            assertTrue(array(carrier, "fieldPath").isEmpty());
        }
        assertTrue(array(unrelated, "sharedCarriers").isEmpty());
    }

    // ----- admission and import -------------------------------------------

    /**
     * A map state and a scalar field are one import path.
     *
     * <p>They are admitted by one {@code versionsFault}, wrapped by one
     * {@code versionsRecord}, indexed by one slice and lowered by one model.
     * The one thing that separates them is the shape of the expression a
     * version carries, which is what the design asks for - and the schema
     * rules that keep the two apart are checked here rather than assumed,
     * because a map state read as a scalar value is exactly the confusion a
     * shared envelope invites.</p>
     */
    @Test
    public void aMapStateRecordTravelsTheScalarImportPath() {
        JsonObject mapEnvelope = RecordedMapStateFixtures
                .twoWriterMapEnvelope(false, true);
        SharedStateEvidence.normalizeGuards(mapEnvelope);
        assertEquals("", SharedStateEvidence.versionsFault(mapEnvelope));
        assertEquals(RecordedMapStateFixtures.MAP_LOCATION,
                SharedStateEvidence.locationKey(mapEnvelope));
        assertTrue(SharedStateEvidence.isMapState(
                RecordedMapStateFixtures.MAP_LOCATION));

        JsonObject mapRecord = RecordedMapStateFixtures.mapVersionsRecord(
                mapEnvelope);
        assertTrue(SharedStateEvidence.isVersionsRecord(mapRecord));

        JsonObject scalarEnvelope = RecordedSharedStateFixtures
                .twoWriterEnvelope(SharedStateEvidence.RESOLUTION_GUARDED,
                        "AMBIGUOUS_WRITERS", 0L);
        SharedStateEvidence.normalizeGuards(scalarEnvelope);
        JsonObject scalarRecord = RecordedSharedStateFixtures.versionsRecord(
                scalarEnvelope, "example.State#value");
        assertTrue(SharedStateEvidence.isVersionsRecord(scalarRecord));

        // One member, both shapes, one projection.
        JsonObject member = SharedStateEvidence.recorded(
                Arrays.asList(scalarRecord, mapRecord),
                SharedStateEvidence.ledgerRecord(
                        RecordedMapStateFixtures.mapAndScalarLedger(),
                        RecordedSharedStateFixtures.identity("REGION.reader",
                                1L)));
        JsonObject row = new JsonObject();
        row.add(SharedStateEvidence.RECORDED_FIELD, member);
        JsonObject guardedMap = RecordedMapStateFixtures
                .twoWriterGuardedMapRead(false);
        SharedStateEvidence.normalizeGuards(guardedMap);
        JsonObject guardedScalar = RecordedSharedStateFixtures.guardedRead(
                21L, 7L, 24);
        SharedStateEvidence.normalizeGuards(guardedScalar);
        // One predicate mentioning both reads, so one projection has to carry
        // both shapes.
        RecordedSessionModel model = RecordedSessionModel.of(
                Collections.singletonList(row),
                RecordedSharedStateFixtures.binary(guardedMap, "==",
                        guardedScalar), "REGION.0");

        Set<String> locations = new LinkedHashSet<>();
        for (JsonElement element
                : array(model.slice().toJson(), "nodes")) {
            String location = string(element.getAsJsonObject(),
                    "locationKey");
            if (!location.isEmpty()) locations.add(location);
        }
        assertTrue(locations.toString(), locations.contains(
                RecordedMapStateFixtures.MAP_LOCATION));
        assertTrue(locations.toString(),
                locations.contains("INSTANCE_FIELD/7#24"));

        // Both reads reached the same lowering, and each says which shape it
        // came from.
        Set<String> kinds = new LinkedHashSet<>();
        JsonObject mapChoice = new JsonObject();
        for (JsonElement element
                : array(model.manifest(), "readChoices")) {
            JsonObject choice = element.getAsJsonObject();
            kinds.add(string(choice, "locationKind"));
            if (RecordedMapStateFixtures.MAP_LOCATION.equals(
                    string(choice, "locationKey"))) {
                mapChoice = choice;
            }
        }
        assertEquals(new LinkedHashSet<>(Arrays.asList(
                        SharedStateEvidence.LOCATION_KIND_MAP_STATE,
                        "INSTANCE_FIELD")), kinds);
        assertEquals(3, array(mapChoice, "candidates").size());
        assertEquals(2, model.boundedWriterUniverses().size());

        // The schema rules that keep the two shapes apart.
        JsonObject wrongSlot = RecordedMapStateFixtures
                .twoWriterMapEnvelope(false, true);
        wrongSlot.getAsJsonObject("location").addProperty("slot", 24);
        assertEquals("envelope names no addressable location",
                SharedStateEvidence.versionsFault(wrongSlot));

        JsonObject scalarValueInAMap = RecordedMapStateFixtures
                .twoWriterMapEnvelope(false, true);
        SharedStateEvidence.normalizeGuards(scalarValueInAMap);
        scalarValueInAMap.getAsJsonArray("versions").get(0).getAsJsonObject()
                .addProperty("versionKind", "WRITE");
        assertTrue(SharedStateEvidence.versionsFault(scalarValueInAMap)
                .contains("that its location kind does not publish"));

        JsonObject stateInAField = RecordedSharedStateFixtures
                .twoWriterEnvelope(SharedStateEvidence.RESOLUTION_GUARDED,
                        "AMBIGUOUS_WRITERS", 0L);
        SharedStateEvidence.normalizeGuards(stateInAField);
        stateInAField.getAsJsonArray("versions").get(0).getAsJsonObject()
                .addProperty("versionKind", "STATE_PUT");
        assertTrue(SharedStateEvidence.versionsFault(stateInAField)
                .contains("that its location kind does not publish"));
    }

    /**
     * Every whole-state mutation the VM publishes is an admitted kind.
     *
     * <p>A version's {@code versionKind} is the VM's own vocabulary:
     * {@code SharedFieldVersions::version_label} writes {@code STATE_} plus
     * the operation {@code ContainerSupport::publish_state} was called with,
     * and those calls are enumerated in {@code symbolicMap.cpp} and
     * {@code symbolicSet.cpp}.  An operation this side does not name is not a
     * tolerated unknown: {@code versionsFault} rejects the <em>whole</em>
     * envelope on the first unadmitted version, so the location loses every
     * version it published and each read of it reaches the formula with no
     * read-from arm at all.  That is what happened to HDFS-11741's DataNode
     * key map, whose {@code removeExpiredKeys()} publishes
     * {@code STATE_REMOVE_IF}, so the vocabulary is pinned here rather than
     * discovered in a campaign.</p>
     */
    @Test
    public void everyPublishedWholeStateMutationIsAnAdmittedVersionKind() {
        for (String operation : Arrays.asList("PUT", "REMOVE", "REMOVE_IF",
                "CLEAR", "REMOVE_AT", "CLEAR_VIEW", "ADD")) {
            JsonArray versions = new JsonArray();
            versions.add(RecordedMapStateFixtures.stateVersion(
                    RecordedMapStateFixtures.WRITER_A_VERSION,
                    "STATE_" + operation, "REGION.writerA", "TASK.a",
                    RecordedMapStateFixtures.writerAState(), null));
            JsonObject envelope =
                    RecordedMapStateFixtures.mapVersionsEnvelope(
                            versions, new JsonArray(), true);
            SharedStateEvidence.normalizeGuards(envelope);
            assertEquals("STATE_" + operation + " is a kind the VM publishes",
                    "", SharedStateEvidence.versionsFault(envelope));
        }
    }

    // ----- two equal-valued writers ---------------------------------------

    /**
     * Two writers that installed the same map state are still two arms.
     *
     * <p>The states are identical expressions, so no value comparison can
     * separate them - which is the case the design is about. The formula must
     * still offer two selectors, two value implications, two read cuts and
     * two evidence rows, and must never fold them into one.</p>
     */
    @Test
    public void twoEqualValuedMapWritersRemainDifferentArms()
            throws Exception {
        ConcolicSmtComposer.Result result = RecordedMapStateFixtures
                .composedMapGolden(folder(), true, true);
        String smt = result.smtLib;

        for (String selector : new String[]{RF1, RF2, RF_UNKNOWN}) {
            assertTrue(smt, smt.contains("(declare-const " + selector
                    + " Bool)"));
        }
        assertNotEquals(RF1, RF2);
        // Exactly one of the three, over all three: the arms compete, they do
        // not accumulate.
        assertTrue(smt, smt.contains("(= (+ (ite " + RF1 + " 1 0) (ite " + RF2
                + " 1 0) (ite " + RF_UNKNOWN + " 1 0)) 1)"));

        String first = assertionBody(smt, "recorded_read_value__41__rf1");
        String second = assertionBody(smt, "recorded_read_value__41__rf2");
        assertTrue(first, first.contains(RF1));
        assertTrue(second, second.contains(RF2));
        assertFalse(first, first.contains(RF2));
        assertFalse(second, second.contains(RF1));
        // Equal states, so the two value terms agree; two arms, so the two
        // implications do not become one.
        assertNotEquals(first, second);
        assertEquals(first.replace(RF1, "S"), second.replace(RF2, "S"));

        // Each arm carries its own cut, over its own write.
        assertTrue(smt, smt.contains("recorded_read_cut__41__31"));
        assertTrue(smt, smt.contains("recorded_read_cut__41__32"));

        List<JsonObject> arms = readFromBindings(result.manifest);
        assertEquals(3, arms.size());
        Set<String> names = new LinkedHashSet<>();
        for (JsonObject arm : arms) {
            names.add(string(arm, "arm"));
            assertEquals(SharedStateEvidence.LOCATION_KIND_MAP_STATE,
                    string(arm, "locationKind"));
            assertEquals(RecordedMapStateFixtures.MAP_LOCATION,
                    string(arm, "locationKey"));
        }
        assertEquals(new LinkedHashSet<>(Arrays.asList("rf1", "rf2",
                SharedStateEvidence.UNKNOWN_WRITER_SELECTOR)), names);
    }

    // ----- the selector decides the value ---------------------------------

    /**
     * Selecting the other arm changes what the reader reads.
     *
     * <p>Writer A put a value at the queried key and writer B removed it, so
     * the two arms are the same container query over two different states.
     * The check is that the <em>value</em> equality differs, not only the
     * order constraints: an arm that changed nothing but the cut would be
     * order-only metadata, and a solver could then take one writer's value
     * under another writer's order.</p>
     */
    @Test
    public void changingTheSelectedArmChangesTheReaderExpression()
            throws Exception {
        ConcolicSmtComposer.Result result = RecordedMapStateFixtures
                .composedMapGolden(folder(), false, true);
        String smt = result.smtLib;

        String first = assertionBody(smt, "recorded_read_value__41__rf1");
        String second = assertionBody(smt, "recorded_read_value__41__rf2");
        // Both are value equalities on the one read constant, and they are
        // different values.
        assertTrue(first, first.contains("(= rf_value__41 "));
        assertTrue(second, second.contains("(= rf_value__41 "));
        assertNotEquals(first.replace(RF1, "S"), second.replace(RF2, "S"));

        // The container lowering is the one canonical codec's: the arm is
        // that writer's state read at the query's key.
        assertTrue(first, first.contains("assoc_"));
        assertTrue(second, second.contains("assoc_"));
        // Writer B's state carries a member writer A's does not, so the two
        // queries answer over two different maps and not over one.
        assertFalse(first, first.contains("777"));
        assertTrue(second, second.contains("777"));

        // Value, guard and order move together on the same selector name.
        String guard = assertionBody(smt, "recorded_write_guard__41__rf2");
        assertTrue(guard, guard.startsWith("(=> " + RF2 + " "));
        String cut = assertionBody(smt, "recorded_read_cut__41__32");
        assertTrue(cut, cut.contains(RF2));
        assertTrue(cut, cut.contains("event_position__32"));
        assertTrue(cut, cut.contains("event_position__41"));
        // The competing write is either before the selected one or after the
        // read; nothing else is ordered.
        assertTrue(smt, smt.contains("recorded_read_cut_outside__41__32__31"));

        // The unknown arm constrains nothing but the value, which is what
        // keeps the choice satisfiable when the order rules the rest out.
        String unknown = assertionBody(smt,
                "recorded_read_value__41__rf_unknown");
        assertTrue(unknown, unknown.contains(RF_UNKNOWN));
        assertFalse(unknown, unknown.contains("event_position__"));
    }

    @Test
    public void exactMapCarrierBindsFatalOwnerToConsumerPort()
            throws Exception {
        ConcolicSmtComposer.Result result = RecordedMapStateFixtures
                .composedExactCarrierGolden(folder());
        String smt = result.smtLib;
        String target = "port__REGION_0_in_0__instance__"
                + "REGION_0_Test_call30";
        String fatal = assertionBody(smt, "fatal_path");
        assertTrue(fatal, fatal.contains("assoc_has " + target));
        assertTrue(fatal, fatal.contains("assoc_read " + target));
        // The realistic VM spelling M_L'java/util/HashMap'_9 sanitizes to
        // this identifier only when it was left as an unconstrained root.
        assertFalse(smt, smt.contains("sym__fatal_"
                + "REGION_0_Test_call30__M_L_java_util_HashMap__9"));
    }

    // ----- named gaps ------------------------------------------------------

    /**
     * Unsupported mutation and missing writer coverage are named, not
     * silently absorbed.
     */
    @Test
    public void openWriterCoverageProducesNamedGaps() throws Exception {
        // An unsupported mutator marks the location incomplete in the VM; the
        // Java side must report it twice over - once as the slice's finding
        // about the location, once as the universe's about the choice - and
        // must call the whole model partial.
        ConcolicSmtComposer.Result incomplete = RecordedMapStateFixtures
                .composedMapGolden(folder(), false, false);
        Set<String> reasons = coverageReasons(incomplete.manifest);
        assertTrue(reasons.toString(), reasons.contains(
                SessionTargetSlice.INCOMPLETE_WRITER_SET));
        assertTrue(reasons.toString(), reasons.contains(
                BoundedWriterUniverse.RECORDED_WRITER_SET_INCOMPLETE));
        assertFalse(incomplete.manifest.toString(),
                bool(incomplete.manifest, "recordedModelComplete", true));
        // The unconditional unknown arm is retained.
        assertTrue(incomplete.smtLib,
                incomplete.smtLib.contains(RF_UNKNOWN));

        // A materialized writer the arms do not carry is a missing writer,
        // and the enumeration is what notices.
        JsonObject envelope = RecordedMapStateFixtures.twoWriterMapEnvelope(
                false, true);
        envelope.getAsJsonArray("versions").add(
                RecordedMapStateFixtures.stateVersion(
                        RecordedMapStateFixtures.INITIAL_VERSION, "INITIAL",
                        "REGION.writerA", "TASK.a",
                        RecordedMapStateFixtures.state("M_MAP_allKeys"),
                        null));
        SharedStateEvidence.normalizeGuards(envelope);
        JsonObject guarded = RecordedMapStateFixtures
                .twoWriterGuardedMapRead(false);
        SharedStateEvidence.normalizeGuards(guarded);
        ConcolicSmtComposer.Result missing = RecordedMapStateFixtures
                .composed(folder(), envelope, RecordedSharedStateFixtures
                        .binary(guarded, "==",
                                RecordedSharedStateFixtures.constant(1)));
        Set<String> missingReasons = coverageReasons(missing.manifest);
        assertTrue(missingReasons.toString(), missingReasons.contains(
                BoundedWriterUniverse.WRITER_WITHOUT_ARM));
        assertTrue(missing.manifest.toString(), missing.manifest.toString()
                .contains("recorded write 30"));

        // The occurrence axis of the product is this run's, and every
        // enumerated read says so rather than reading as a closed universe.
        assertTrue(missingReasons.toString(), missingReasons.contains(
                BoundedWriterUniverse.SEMANTIC_OCCURRENCE_COVERAGE_OPEN));
        JsonObject universe = array(object(missing.manifest,
                "recordedSessionModel"), "writerUniverses").get(0)
                .getAsJsonObject();
        assertEquals(BoundedWriterUniverse.KIND, string(universe, "kind"));
        assertEquals(RecordedMapStateFixtures.MAP_LOCATION,
                string(universe, "locationKey"));
        assertFalse(universe.get("closed").getAsBoolean());
        assertTrue(universe.get("retainsUnknownArm").getAsBoolean());
        assertEquals(2, universe.get("materializedCases").getAsInt());
    }

    /**
     * The two structural facts that make a map arm a real alternative.
     *
     * <p>An arm must read the state <em>its own</em> writer published, and
     * every arm of one read must query the same key. Either failing would
     * mean the selector changes something other than the writer, so both are
     * refusals rather than observations.</p>
     */
    @Test
    public void aMapArmMustQueryItsOwnWriterAtTheSharedKey() {
        JsonObject envelope = RecordedMapStateFixtures.twoWriterMapEnvelope(
                false, true);
        SharedStateEvidence.normalizeGuards(envelope);
        JsonObject record = RecordedMapStateFixtures.mapVersionsRecord(
                envelope);

        JsonObject honest = RecordedMapStateFixtures
                .twoWriterGuardedMapRead(false);
        SharedStateEvidence.normalizeGuards(honest);
        BoundedWriterUniverse closedButForOccurrences =
                BoundedWriterUniverse.of(honest, record);
        assertEquals(Collections.singletonList(
                        BoundedWriterUniverse.SEMANTIC_OCCURRENCE_COVERAGE_OPEN),
                reasons(closedButForOccurrences.gaps()));
        assertTrue(closedButForOccurrences.toJson().get("mapState")
                .getAsBoolean());
        assertEquals(2, closedButForOccurrences.toJson()
                .get("materializedCases").getAsInt());

        // rf2 reading writer A's state: selecting it would hand the reader
        // another writer's value under writer B's order.
        JsonObject stolen = RecordedMapStateFixtures
                .twoWriterGuardedMapRead(false);
        stolen.getAsJsonArray("candidates").get(1).getAsJsonObject().add(
                "expression", RecordedMapStateFixtures.query(
                        RecordedMapStateFixtures.writerAState(),
                        RecordedSharedStateFixtures.constant(4242)));
        SharedStateEvidence.normalizeGuards(stolen);
        assertTrue(reasons(BoundedWriterUniverse.of(stolen, record).gaps())
                .contains(BoundedWriterUniverse.ARM_STATE_NOT_ITS_WRITER));

        // Two arms over two different keys: the choice would be over what was
        // asked and not over who wrote it.
        JsonObject otherKey = RecordedMapStateFixtures
                .twoWriterGuardedMapRead(false);
        otherKey.getAsJsonArray("candidates").get(1).getAsJsonObject().add(
                "expression", RecordedMapStateFixtures.query(
                        RecordedMapStateFixtures.writerBState(false),
                        RecordedSharedStateFixtures.constant(7)));
        SharedStateEvidence.normalizeGuards(otherKey);
        assertTrue(reasons(BoundedWriterUniverse.of(otherKey, record).gaps())
                .contains(BoundedWriterUniverse.INCOMPATIBLE_QUERY_KEY));

        // No admitted store at all: the arms are all there is to see, and
        // that is precisely what cannot be called complete.
        BoundedWriterUniverse blind = BoundedWriterUniverse.of(honest, null);
        assertTrue(reasons(blind.gaps()).contains(
                BoundedWriterUniverse.NO_RECORDED_VERSION_STORE));
        assertTrue(reasons(blind.gaps()).contains(
                BoundedWriterUniverse.UNRECORDED_WRITER_CASE));
        assertEquals(0, blind.toJson().get("materializedCases").getAsInt());
    }

    // ----- parity -----------------------------------------------------------

    /** The map query reaches the model as the same census the SMT is. */
    @Test
    public void theCensusAndTheFormulaProjectOneMapModel() throws Exception {
        ConcolicSmtComposer.Result result = RecordedMapStateFixtures
                .composedMapGolden(folder(), false, true);
        JsonObject model = CanonicalSessionModel.read(result.manifest);
        assertTrue(CanonicalSessionModel.isModel(model));
        // A map state and a map query are counted by the model as the same
        // two kinds a field version and a field read are.
        JsonObject counts = model.getAsJsonObject("counts");
        assertEquals(model.toString(), 2,
                counts.get("fieldVersions").getAsInt());
        assertEquals(model.toString(), 1,
                counts.get("fieldReads").getAsInt());
    }

    // ----- the VM bridge ----------------------------------------------------

    /**
     * A stock JDK has neither map native, so both calls answer with the same
     * named gap the handoff and field bridges answer with. Silence would be
     * indistinguishable from a map that recorded nothing.
     */
    @Test
    public void theMapCarrierBridgeNamesItsAbsenceOnAStockJdk() {
        for (String native0 : new String[]{"selectSharedMapCarrier",
                "getSharedMapVersions"}) {
            boolean present = true;
            try {
                System.class.getMethod(native0, Object.class);
            } catch (NoSuchMethodException absent) {
                present = false;
            }
            assertFalse(native0, present);
        }

        ConcolicRegionRuntime.SharedStateResult selected =
                ConcolicRegionRuntime.selectSharedMapCarrier(
                        new java.util.HashMap<String, String>());
        assertFalse(selected.ok());
        assertEquals(SharedStateEvidence.API_UNAVAILABLE, selected.status());
        assertEquals("SHARED_STATE_API_UNAVAILABLE", selected.reason());
        assertEquals(SharedStateEvidence.STAGE_SELECT, selected.stage());
        assertTrue(SharedStateEvidence.isGap(selected.gap()));
        assertEquals(0, selected.record().size());

        ConcolicRegionRuntime.SharedStateResult captured =
                ConcolicRegionRuntime.captureSharedMapVersions(
                        new java.util.HashMap<String, String>());
        assertFalse(captured.ok());
        assertEquals(SharedStateEvidence.API_UNAVAILABLE, captured.status());
        assertEquals(SharedStateEvidence.STAGE_VERSIONS, captured.stage());
        assertTrue(SharedStateEvidence.isGap(captured.gap()));

        // A missing map is missing metadata, never a guess about which map.
        for (ConcolicRegionRuntime.SharedStateResult absent
                : new ConcolicRegionRuntime.SharedStateResult[]{
                ConcolicRegionRuntime.selectSharedMapCarrier(null),
                ConcolicRegionRuntime.captureSharedMapVersions(null)}) {
            assertFalse(absent.ok());
            assertEquals(SharedStateEvidence.MISSING_METADATA,
                    absent.status());
            assertTrue(SharedStateEvidence.isGap(absent.gap()));
        }
    }

    // ----- helpers ----------------------------------------------------------

    private Path folder() throws Exception {
        return temporary.newFolder().toPath();
    }

    /** The term of one named assertion in the emitted formula. */
    private static String assertionBody(String smt, String name) {
        String marker = ":named " + name + ")";
        int end = smt.indexOf(marker);
        assertTrue("no assertion named " + name + " in\n" + smt, end >= 0);
        int open = smt.lastIndexOf("(assert (! ", end);
        assertTrue("assertion " + name + " has no opening in\n" + smt,
                open >= 0);
        return smt.substring(open + "(assert (! ".length(), end).trim();
    }

    private static List<JsonObject> readFromBindings(JsonObject manifest) {
        List<JsonObject> rows = new ArrayList<>();
        for (JsonElement element
                : array(manifest, "recordedValueBindings")) {
            JsonObject row = element.getAsJsonObject();
            if ("RECORDED_READ_FROM_VALUE_BINDING".equals(
                    string(row, "kind"))
                    && longInteger(row, "readEventId", 0L)
                    == RecordedMapStateFixtures.QUERY_EVENT) {
                rows.add(row);
            }
        }
        return rows;
    }

    private static Set<String> coverageReasons(JsonObject manifest) {
        Set<String> reasons = new LinkedHashSet<>();
        for (JsonElement element : array(manifest, "coverageGaps")) {
            reasons.add(string(element.getAsJsonObject(), "reason"));
        }
        return reasons;
    }

    private static List<String> reasons(List<JsonObject> gaps) {
        List<String> reasons = new ArrayList<>();
        for (JsonObject gap : gaps) reasons.add(string(gap, "reason"));
        return reasons;
    }
}
