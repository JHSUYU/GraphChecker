package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * The recorded-order rotation race, derived from the write order the VM
 * recorded rather than from the shape of the witness.
 *
 * <p>The arrangement under test is hdfs-17899-bug3's: the target datanode's
 * {@code allKeys} is read at event 233, its candidate writers are the versions
 * below that, and the datanode installs the key the wire is naming at versions
 * 247 onwards -- after the read that goes looking for it. A model that takes
 * the last of the recorded predecessors is then describing a real rotation
 * race and not a hole in the analysis.</p>
 */
public class RecordedOrderRaceTest {

    private static final String LOCATION = "MAP_STATE/100#-3";

    /** The race: last recorded writer taken, later write at the location. */
    @Test
    public void lastRecordedWriterWithALaterWriteIsARace() {
        JsonObject race = RecordedOrderRace.of(
                manifest(armsBelowTheRead(), laterWrites(247L, 266L)),
                fatalArms(), model("read_selector__w2"));

        assertNotNull(race);
        assertEquals(RecordedOrderRace.KIND, race.get("kind").getAsString());
        assertEquals(LOCATION, race.get("sessionLocationKey").getAsString());
        assertEquals(233L, race.get("readEventId").getAsLong());
        assertEquals(210L, race.get("selectedWriterVersionId").getAsLong());
        assertEquals("the earliest write after the read is the one it raced",
                247L, race.get("laterWriterVersionId").getAsLong());
        assertTrue(race.get("detail").getAsString()
                .contains("rotation race"));
    }

    /**
     * An earlier predecessor is the model declining a write the program had
     * already done, which is a different thing and not this finding.
     */
    @Test
    public void anEarlierPredecessorIsNotARace() {
        assertNull(RecordedOrderRace.of(
                manifest(armsBelowTheRead(), laterWrites(247L)),
                fatalArms(), model("read_selector__w1")));
    }

    /** With nothing written after the read there is no race to report. */
    @Test
    public void noWriteAfterTheReadIsNoRace() {
        assertNull(RecordedOrderRace.of(
                manifest(armsBelowTheRead(), new JsonArray()),
                fatalArms(), model("read_selector__w2")));
    }

    /** A write after the read to some other location is another story. */
    @Test
    public void aLaterWriteElsewhereIsNotThisReadsRace() {
        JsonArray elsewhere = laterWrites(247L);
        elsewhere.get(0).getAsJsonObject()
                .addProperty("sessionLocationKey", "MAP_STATE/11#-3");

        assertNull(RecordedOrderRace.of(
                manifest(armsBelowTheRead(), elsewhere),
                fatalArms(), model("read_selector__w2")));
    }

    /**
     * The initial arm is the absence of a writer. A witness that takes it is
     * the free-initial-arm freedom, which blocks; calling it a race would
     * launder exactly the case the ruling still refuses.
     */
    @Test
    public void theInitialArmIsNeverARace() {
        assertNull(RecordedOrderRace.of(
                manifest(armsBelowTheRead(), laterWrites(247L)),
                fatalArms(), model("read_selector__initial")));
    }

    /**
     * A manifest published before the order rows existed carries no race.
     * Answering "no" there is the honest reading; guessing from arm position
     * would invent an order the recording never stated.
     */
    @Test
    public void aManifestWithoutOrderRowsCarriesNoRace() {
        JsonArray arms = armsBelowTheRead();
        for (int index = 0; index < arms.size(); index++) {
            arms.get(index).getAsJsonObject().remove(
                    RecordedOrderRace.WRITER_VERSION);
            arms.get(index).getAsJsonObject().remove(
                    RecordedOrderRace.READ_EVENT);
        }
        List<JsonObject> fatal = new ArrayList<>();
        for (int index = 0; index < arms.size(); index++) {
            fatal.add(arms.get(index).getAsJsonObject());
        }

        assertNull(RecordedOrderRace.of(
                manifest(arms, laterWrites(247L)), fatal,
                model("read_selector__w2")));
    }

    /** Nothing selected is nothing to say. */
    @Test
    public void noSelectedArmIsNoRace() {
        assertNull(RecordedOrderRace.of(
                manifest(armsBelowTheRead(), laterWrites(247L)),
                fatalArms(), new LinkedHashMap<String, String>()));
    }

    // ---- fixtures ---------------------------------------------------------

    /** The fatal read's own arms: one initial and two recorded writers. */
    private static JsonArray armsBelowTheRead() {
        JsonArray arms = new JsonArray();
        arms.add(arm("read_selector__initial", "INITIAL_SOURCE.a706a1a",
                -1L, 233L));
        arms.add(arm("read_selector__w1", "region:REGION.addKeys", 120L,
                233L));
        arms.add(arm("read_selector__w2", "region:REGION.addKeys", 210L,
                233L));
        return arms;
    }

    /** Writes to the same location a later read of it retained. */
    private static JsonArray laterWrites(long... versions) {
        JsonArray arms = new JsonArray();
        for (long version : versions) {
            JsonObject row = arm("read_selector__later" + version,
                    "region:REGION.addKeys", version, 300L);
            row.addProperty("readIdentity", "RFC.later");
            arms.add(row);
        }
        return arms;
    }

    private static JsonObject arm(String selector, String owner,
                                  long version, long readEvent) {
        JsonObject row = new JsonObject();
        row.addProperty("kind", "DIRECT_GUARDED_READ_ARM");
        row.addProperty("selector", selector);
        row.addProperty("readIdentity", "RFC.fatal");
        row.addProperty("sessionLocationKey", LOCATION);
        row.addProperty("locationKey", "MAP_STATE/d88858a6#-3");
        row.addProperty("writerCaseOwner", owner);
        row.addProperty("initialState", owner.startsWith("INITIAL_SOURCE"));
        row.addProperty(RecordedOrderRace.WRITER_VERSION, version);
        row.addProperty(RecordedOrderRace.READ_EVENT, readEvent);
        return row;
    }

    /** A manifest whose guarded-read model holds both reads' arms. */
    private static JsonObject manifest(JsonArray fatal, JsonArray later) {
        JsonObject fatalRead = new JsonObject();
        fatalRead.addProperty("readIdentity", "RFC.fatal");
        fatalRead.add("arms", fatal);
        JsonObject laterRead = new JsonObject();
        laterRead.addProperty("readIdentity", "RFC.later");
        laterRead.add("arms", later);
        JsonArray reads = new JsonArray();
        reads.add(fatalRead);
        reads.add(laterRead);
        JsonObject model = new JsonObject();
        model.add("reads", reads);
        JsonObject manifest = JsonParser.parseString(
                "{\"fatalSite\":\"BlockTokenSecretManager"
                + ".retrieveDataEncryptionKey#u8\"}").getAsJsonObject();
        manifest.add("guardedReadModel", model);
        return manifest;
    }

    /** The fatal read's arms as the reach report projects them. */
    private static List<JsonObject> fatalArms() {
        JsonArray arms = armsBelowTheRead();
        List<JsonObject> rows = new ArrayList<>();
        for (int index = 0; index < arms.size(); index++) {
            rows.add(arms.get(index).getAsJsonObject());
        }
        return rows;
    }

    private static Map<String, String> model(String selected) {
        Map<String, String> values = new LinkedHashMap<>();
        values.put(selected, "true");
        return values;
    }
}
