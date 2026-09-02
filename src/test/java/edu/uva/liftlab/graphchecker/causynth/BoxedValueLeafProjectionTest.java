package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * The one shape exempt from the unclosed-reference demotion: a JDK boxing
 * wrapper's own value.
 *
 * <p>The demotion exists because a primitive reached through a transferred
 * reference has a writer this model does not hold, and inventing a fresh
 * solver leaf for it would claim a freedom the run never had.  A wrapper
 * breaks that premise rather than escaping it: {@code Boolean.FALSE.value}
 * has no writer because it <em>cannot</em> have one, so the producer of the
 * value is the producer of the reference - which the carrier edge already
 * names.</p>
 *
 * <p>What these tests pin is that the exemption is exactly that narrow. It
 * needs the wrapper type, it needs the carrier of this very object rather than
 * of something the object was later reached from, and everything else keeps
 * the demotion and keeps it named.</p>
 */
public class BoxedValueLeafProjectionTest {
    private static final String REGION = "REGION.client";
    private static final String PRODUCER_REGION = "REGION.main";
    private static final String OCCURRENCE =
            "node/client#epoch0/region/" + REGION + "#1";
    private static final String PRODUCER_OCCURRENCE =
            "node/main#epoch0/region/" + PRODUCER_REGION + "#1";
    private static final String CARRIER_PORT = REGION + ".in.carrier";
    private static final String LEAF_PORT = REGION + ".in.leaf";
    private static final String BOXED_VALUE = "<java.lang.Boolean: boolean "
            + "value>";
    private static final String PLAIN_VALUE = "<example.Holder: int value>";
    /** The wrapper object the carrier edge delivered. */
    private static final int WRAPPER = 6;

    /**
     * The leaf keeps its symbolic demand and gains the producer the reference
     * already had.  Everything the carrier proves is carried over verbatim -
     * the writer, the two ordinals and the field whose read-from is still
     * undecided - so deciding that writer decides this leaf.
     */
    @Test
    public void aBoxedLeafIsProjectedOntoItsCarriersProducer() {
        List<Map<String, Object>> regions = regions(leaf(BOXED_VALUE,
                WRAPPER));
        List<Map<String, Object>> edges = new ArrayList<>(
                Collections.singletonList(carrier(WRAPPER)));

        RuntimeSelectedRegionFinalizer.markUnclosedReferenceLeavesConcrete(
                regions, edges, Collections.<Map<String, Object>>emptyList(),
                Collections.<String, String>emptyMap());

        Map<String, Object> leaf = port(regions, LEAF_PORT);
        assertNull(String.valueOf(leaf), leaf.get("symbolicDemand"));

        Map<String, Object> projection = projection(edges);
        assertNotNull(String.valueOf(edges), projection);
        assertEquals("RUNTIME_FIELD_FLOW", projection.get("kind"));
        assertEquals(PRODUCER_OCCURRENCE,
                projection.get("fromOccurrenceId"));
        assertEquals(OCCURRENCE, projection.get("toOccurrenceId"));
        assertEquals(LEAF_PORT, projection.get("toPort"));
        assertEquals(DependencyRole.VALUE_FRONTIER,
                projection.get("dependencyRole"));
        // Whatever the carrier proves about its writer, the projection states
        // for the leaf, under the same still-undecided read-from address.
        assertEquals("example.Client#raiseRequest",
                projection.get("readFromField"));
        assertEquals(11L, projection.get("writerEventSeq"));
        assertEquals(21L, projection.get("readerEventSeq"));
        // The carrier itself is untouched: it still closes its own port.
        assertEquals(CARRIER_PORT, carrier(edges).get("toPort"));
    }

    /**
     * The exemption is about wrappers, not about primitives in general.  A
     * plain object's field reached through a delivered reference has a writer
     * this model does not hold, and it keeps the named under-approximation.
     */
    @Test
    public void aPlainReferenceLeafIsStillDemotedByName() {
        List<Map<String, Object>> regions = regions(leaf(PLAIN_VALUE,
                WRAPPER));
        List<Map<String, Object>> edges = new ArrayList<>(
                Collections.singletonList(carrier(WRAPPER)));

        RuntimeSelectedRegionFinalizer.markUnclosedReferenceLeavesConcrete(
                regions, edges, Collections.<Map<String, Object>>emptyList(),
                Collections.<String, String>emptyMap());

        Map<String, Object> leaf = port(regions, LEAF_PORT);
        assertEquals("CONCRETE_REFERENCE_BOUNDARY_REPLAY",
                leaf.get("symbolicDemand"));
        assertNull(String.valueOf(edges), projection(edges));
    }

    /**
     * A leaf the <em>consumer</em> installs itself was never reached through
     * the boundary, so it is not demoted and not projected - not even when it
     * is a wrapper whose reference a carrier did deliver.
     */
    @Test
    public void aLeafTheConsumerWritesItselfIsNeitherDemotedNorProjected() {
        List<Map<String, Object>> regions = regions(leaf(BOXED_VALUE,
                WRAPPER));
        List<Map<String, Object>> edges = new ArrayList<>(
                Collections.singletonList(carrier(WRAPPER)));
        List<Map<String, Object>> graph = Collections.singletonList(
                heapWriteLeaf(WRAPPER, BOXED_VALUE));

        RuntimeSelectedRegionFinalizer.markUnclosedReferenceLeavesConcrete(
                regions, edges, graph, Collections.singletonMap(
                        REGION + "\n1", OCCURRENCE));

        Map<String, Object> leaf = port(regions, LEAF_PORT);
        assertNull(String.valueOf(leaf), leaf.get("symbolicDemand"));
        assertNull(String.valueOf(edges), projection(edges));
    }

    /**
     * The immutability argument is about this wrapper object, and one hop
     * further it is not available: a wrapper merely reachable from a delivered
     * object was produced by whatever wrote the field that holds it, and
     * nothing here names that write.  It is demoted like any other unclosed
     * reference leaf.
     */
    @Test
    public void aWrapperReachedOneHopFurtherIsStillDemoted() {
        List<Map<String, Object>> regions = regions(leaf(BOXED_VALUE, 9));
        List<Map<String, Object>> edges = new ArrayList<>(
                Collections.singletonList(carrier(WRAPPER)));
        // The delivered object 6 holds the wrapper 9 in a field this trace
        // observed, so 9 is reachable - and only reachable.
        List<Map<String, Object>> graph = Collections.singletonList(
                heapReadLink(WRAPPER, 9));

        RuntimeSelectedRegionFinalizer.markUnclosedReferenceLeavesConcrete(
                regions, edges, graph, Collections.singletonMap(
                        REGION + "\n1", OCCURRENCE));

        Map<String, Object> leaf = port(regions, LEAF_PORT);
        assertEquals("CONCRETE_REFERENCE_BOUNDARY_REPLAY",
                leaf.get("symbolicDemand"));
        assertNull(String.valueOf(edges), projection(edges));
    }

    /**
     * A leaf a region edge already closes was never at stake, and must not
     * collect a second producer it did not need.
     */
    @Test
    public void anAlreadyClosedLeafIsLeftAlone() {
        List<Map<String, Object>> regions = regions(leaf(BOXED_VALUE,
                WRAPPER));
        Map<String, Object> closing = carrier(WRAPPER);
        closing.put("edgeId", "RF.leaf");
        closing.put("toPort", LEAF_PORT);
        List<Map<String, Object>> edges = new ArrayList<>(
                Arrays.asList(carrier(WRAPPER), closing));

        RuntimeSelectedRegionFinalizer.markUnclosedReferenceLeavesConcrete(
                regions, edges, Collections.<Map<String, Object>>emptyList(),
                Collections.<String, String>emptyMap());

        assertNull(port(regions, LEAF_PORT).get("symbolicDemand"));
        assertNull(String.valueOf(edges), projection(edges));
        assertEquals(2, edges.size());
    }

    /**
     * A wrapper leaf whose receiver no edge delivered is not exempt either:
     * the exemption rests on the reference having a named producer, and this
     * one has none.  It never reaches the demotion at all, because nothing
     * delivered its receiver - so it stays an ordinary symbolic input.
     */
    @Test
    public void aBoxedLeafWithNoDeliveredReceiverIsUntouched() {
        List<Map<String, Object>> regions = regions(leaf(BOXED_VALUE, 42));
        List<Map<String, Object>> edges = new ArrayList<>(
                Collections.singletonList(carrier(WRAPPER)));

        RuntimeSelectedRegionFinalizer.markUnclosedReferenceLeavesConcrete(
                regions, edges, Collections.<Map<String, Object>>emptyList(),
                Collections.<String, String>emptyMap());

        Map<String, Object> leaf = port(regions, LEAF_PORT);
        assertNull(String.valueOf(leaf), leaf.get("symbolicDemand"));
        assertNull(String.valueOf(edges), projection(edges));
    }

    /**
     * Two candidate writers of one carrier stay two candidate producers of the
     * leaf.  Collapsing them here would decide a read-from the recorded
     * evidence has not decided yet, which is the value guess this model defers
     * on purpose.
     */
    @Test
    public void everyCandidateCarrierIsProjected() {
        List<Map<String, Object>> regions = regions(leaf(BOXED_VALUE,
                WRAPPER));
        Map<String, Object> second = carrier(WRAPPER);
        second.put("edgeId", "RF.carrier2");
        second.put("writerEventSeq", 13L);
        List<Map<String, Object>> edges = new ArrayList<>(
                Arrays.asList(carrier(WRAPPER), second));

        RuntimeSelectedRegionFinalizer.markUnclosedReferenceLeavesConcrete(
                regions, edges, Collections.<Map<String, Object>>emptyList(),
                Collections.<String, String>emptyMap());

        List<String> projected = new ArrayList<>();
        for (Map<String, Object> edge : edges) {
            if (String.valueOf(edge.get("edgeId")).startsWith("BX.")) {
                projected.add(String.valueOf(edge.get("toPort")));
            }
        }
        assertEquals(Arrays.asList(LEAF_PORT, LEAF_PORT), projected);
        // Two arms, two identities: one id for two producers would let the
        // canonicalizer keep whichever it saw first.
        assertTrue(edges.get(2).get("edgeId") + " vs "
                        + edges.get(3).get("edgeId"),
                !edges.get(2).get("edgeId").equals(
                        edges.get(3).get("edgeId")));
        assertFalse(projected.isEmpty());
    }

    // ------------------------------------------------------------------
    // Fixture
    // ------------------------------------------------------------------

    private static List<Map<String, Object>> regions(
            Map<String, Object> leaf) {
        Map<String, Object> region = object("regionId", REGION);
        region.put("symbolicInputs", new ArrayList<>(Arrays.asList(
                object("portId", CARRIER_PORT, "occurrenceId", OCCURRENCE,
                        "dependencyRole", DependencyRole.VALUE_FRONTIER,
                        "cell", "<example.Client: java.lang.Boolean "
                                + "raiseRequest>"),
                leaf)));
        region.put("outputs", new ArrayList<Map<String, Object>>());
        return new ArrayList<>(Collections.singletonList(region));
    }

    /** One accessor leaf, as {@code accessorPorts} publishes it. */
    private static Map<String, Object> leaf(String declaration,
                                            int receiver) {
        Map<String, Object> port = object("portId", LEAF_PORT,
                "occurrenceId", OCCURRENCE,
                "sourceKind", "ACCESSOR_RETURN",
                "dependencyRole", DependencyRole.VALUE_FRONTIER,
                "cell", declaration);
        port.put("fieldPathDeclarations",
                Collections.singletonList(declaration));
        port.put("fieldReceiverObjectId", receiver);
        port.put("rootKind", "OBSERVED_FIELD_RECEIVER");
        port.put("rootObjectId", receiver);
        return port;
    }

    /** The edge that delivered the wrapper reference into this activation. */
    private static Map<String, Object> carrier(int deliveredObject) {
        Map<String, Object> edge = object("schemaVersion", 3,
                "kind", "RUNTIME_FIELD_FLOW", "edgeId", "RF.carrier",
                "transportKind", "HEAP",
                "fromRegion", PRODUCER_REGION, "toRegion", REGION,
                "fromPort", PRODUCER_REGION + ".out.raiseRequest",
                "toPort", CARRIER_PORT,
                "fromOccurrenceId", PRODUCER_OCCURRENCE,
                "toOccurrenceId", OCCURRENCE,
                "dependencyRole", DependencyRole.CONCRETE_STRUCTURE_CARRIER,
                "receiverObjectId", 17,
                "valueObjectId", deliveredObject,
                "writerEventSeq", 11L, "readerEventSeq", 21L,
                "readFromField", "example.Client#raiseRequest",
                "readFromProvenance", "TRACE_CANDIDATE_WRITER");
        return edge;
    }

    /** One leaf this activation installs on the delivered object itself. */
    private static Map<String, Object> heapWriteLeaf(int receiver,
                                                     String declaration) {
        Map<String, Object> edge = object("schemaVersion", 3,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "transferKind", "HEAP_WRITE", "id", "DF.write");
        Map<String, Object> binding = object("regionId", REGION,
                "rootCallId", 1L, "fieldReceiverObjectId", receiver);
        binding.put("fieldPathDeclarations",
                Collections.singletonList(declaration));
        edge.put("runtimeFieldBindings",
                Collections.singletonList(binding));
        return edge;
    }

    private static Map<String, Object> heapReadLink(int receiver, int value) {
        Map<String, Object> edge = object("schemaVersion", 3,
                "graphKind", "RUNTIME_REFINED_DATAFLOW",
                "transferKind", "HEAP_READ", "id", "DF.link");
        edge.put("runtimeFieldBindings", Collections.singletonList(
                object("regionId", REGION, "rootCallId", 1L,
                        "fieldReceiverObjectId", receiver,
                        "valueObjectId", value)));
        return edge;
    }

    // ------------------------------------------------------------------
    // Assertions
    // ------------------------------------------------------------------

    @SuppressWarnings("unchecked")
    private static Map<String, Object> port(
            List<Map<String, Object>> regions, String portId) {
        for (Map<String, Object> region : regions) {
            for (Object value : (List<Object>) region.get("symbolicInputs")) {
                Map<String, Object> port = (Map<String, Object>) value;
                if (portId.equals(port.get("portId"))) return port;
            }
        }
        throw new AssertionError("no port " + portId);
    }

    private static Map<String, Object> projection(
            List<Map<String, Object>> edges) {
        Map<String, Object> found = null;
        for (Map<String, Object> edge : edges) {
            if (String.valueOf(edge.get("edgeId")).startsWith("BX.")) {
                assertNull("more than one projection", found);
                found = edge;
            }
        }
        return found;
    }

    private static Map<String, Object> carrier(
            List<Map<String, Object>> edges) {
        for (Map<String, Object> edge : edges) {
            if ("RF.carrier".equals(edge.get("edgeId"))) return edge;
        }
        throw new AssertionError("no carrier edge");
    }

    private static Map<String, Object> object(Object... values) {
        Map<String, Object> result = new LinkedHashMap<>();
        for (int index = 0; index < values.length; index += 2) {
            result.put(String.valueOf(values[index]), values[index + 1]);
        }
        return result;
    }
}
