package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/** One catalog owns the edge evidence; a row owns only the reference. */
public class EdgeBindingCatalogTest {

    @Test
    public void indexesEdgesByTheirOwnId() {
        EdgeBindingCatalog catalog = EdgeBindingCatalog.of(
                Arrays.asList(edge("SF.a"), edge("SF.b")));

        assertEquals(2, catalog.size());
        assertEquals(edge("SF.b"), catalog.hydrate(ids("SF.b")).get(0));
    }

    @Test
    public void refusesADuplicateId() {
        try {
            EdgeBindingCatalog.of(Arrays.asList(edge("SF.a"), edge("SF.a")));
            throw new AssertionError("duplicate edge id accepted");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(), refused.getMessage()
                    .contains("SF.a"));
        }
    }

    @Test
    public void refusesAnEdgeWithNoId() {
        try {
            EdgeBindingCatalog.of(Collections.singletonList(
                    new JsonObject()));
            throw new AssertionError("anonymous edge accepted");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(), refused.getMessage()
                    .contains("unique nonempty ids"));
        }
    }

    /** A reference the catalog cannot name is a corrupt pairing, not a skip. */
    @Test
    public void refusesAnIdTheCatalogDoesNotHold() {
        EdgeBindingCatalog catalog = EdgeBindingCatalog.of(
                Collections.singletonList(edge("SF.a")));
        try {
            catalog.hydrate(ids("SF.missing"));
            throw new AssertionError("unknown edge id accepted");
        } catch (IllegalArgumentException refused) {
            assertEquals("unknown runtime edge id SF.missing",
                    refused.getMessage());
        }
    }

    @Test
    public void refusesARepeatedOrBlankReference() {
        EdgeBindingCatalog catalog = EdgeBindingCatalog.of(
                Collections.singletonList(edge("SF.a")));
        for (JsonArray malformed : Arrays.asList(ids("SF.a", "SF.a"),
                ids(" "), ids(""))) {
            try {
                catalog.hydrate(malformed);
                throw new AssertionError("accepted " + malformed);
            } catch (IllegalArgumentException refused) {
                assertEquals("edgeBindingIds must be unique nonempty strings",
                        refused.getMessage());
            }
        }
    }

    /** Publishing an id for evidence the catalog does not hold would
     *  substitute the catalog's edge for the row's. */
    @Test
    public void refusesABindingThatDiffersFromItsCatalogRow() {
        EdgeBindingCatalog catalog = EdgeBindingCatalog.of(
                Collections.singletonList(edge("SF.a")));
        JsonObject drifted = edge("SF.a");
        drifted.addProperty("kind", "DIFFERENT");
        JsonArray bindings = new JsonArray();
        bindings.add(drifted);
        try {
            catalog.idsOf(bindings);
            throw new AssertionError("drifted binding accepted");
        } catch (IllegalArgumentException refused) {
            assertEquals("edge binding is absent from the edge catalog: SF.a",
                    refused.getMessage());
        }
    }

    /** compact and hydrate are inverses on one row, selection order kept. */
    @Test
    public void aRowRoundTripsThroughItsReferences() {
        EdgeBindingCatalog catalog = EdgeBindingCatalog.of(
                Arrays.asList(edge("SF.a"), edge("SF.b"), edge("SF.c")));
        JsonObject row = new JsonObject();
        row.addProperty("taskId", "TASK.one");
        JsonArray bindings = new JsonArray();
        bindings.add(edge("SF.c"));
        bindings.add(edge("SF.a"));
        row.add(EdgeBindingCatalog.BINDINGS, bindings);
        JsonObject expected = row.deepCopy();

        catalog.compactInto(row);
        assertFalse(row.has(EdgeBindingCatalog.BINDINGS));
        assertEquals(ids("SF.c", "SF.a"),
                row.getAsJsonArray(EdgeBindingCatalog.IDS));

        catalog.hydrateInto(row);
        assertEquals(expected, row);
    }

    /** A row that selected nothing publishes no reference list at all. */
    @Test
    public void anEmptySelectionPublishesNothing() {
        EdgeBindingCatalog catalog = EdgeBindingCatalog.of(
                Collections.singletonList(edge("SF.a")));
        JsonObject row = new JsonObject();
        row.addProperty("taskId", "TASK.none");

        catalog.compactInto(row);
        assertFalse(row.has(EdgeBindingCatalog.IDS));
        catalog.hydrateInto(row);
        assertFalse(row.has(EdgeBindingCatalog.BINDINGS));
    }

    @Test
    public void refusesToCompactATwiceCompactedRow() {
        EdgeBindingCatalog catalog = EdgeBindingCatalog.of(
                Collections.singletonList(edge("SF.a")));
        JsonObject row = new JsonObject();
        row.add(EdgeBindingCatalog.IDS, ids("SF.a"));
        try {
            catalog.compactInto(row);
            throw new AssertionError("re-compaction accepted");
        } catch (IllegalArgumentException refused) {
            assertEquals("row is already binding-compacted",
                    refused.getMessage());
        }
    }

    private static JsonObject edge(String id) {
        JsonObject edge = new JsonObject();
        edge.addProperty("edgeId", id);
        edge.addProperty("kind", "RUNTIME_SHARED_LOCATION");
        edge.addProperty("fromRegion", "REGION.from");
        edge.addProperty("toRegion", "REGION.to");
        return edge;
    }

    private static JsonArray ids(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }
}
