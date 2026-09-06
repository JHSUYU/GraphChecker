package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
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

    // ----- admission and import -------------------------------------------

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

        // ----- named gaps ------------------------------------------------------

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

    private static List<String> reasons(List<JsonObject> gaps) {
        List<String> reasons = new ArrayList<>();
        for (JsonObject gap : gaps) reasons.add(string(gap, "reason"));
        return reasons;
    }
}
