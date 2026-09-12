package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Which container fields are declared as one whole-state location.
 *
 * <p>An indexed field must additionally be reference-stable.  The two shapes
 * this decision has to separate are both real: HDFS-17960's
 * {@code DirectorySnapshottableFeature#snapshotsByNames} is
 * {@code private final List<Snapshot> = new ArrayList<>()}, while
 * {@code INodeDirectory#children} is {@code private List<INode> = null} and
 * allocated on first use.  The fixtures below have exactly those shapes.</p>
 */
public class IndexedCarrierDeclarationTest {

    /** The shape of DirectorySnapshottableFeature#snapshotsByNames. */
    static final class StableOwner {
        final List<Object> rows = new ArrayList<Object>();
        final Map<Object, Object> entries = new HashMap<Object, Object>();
    }

    /** The shape of INodeDirectory#children. */
    static final class LazyOwner {
        List<Object> rows = null;
        Map<Object, Object> entries = null;
    }

    @Test
    public void aFinalListFieldIsDeclaredAsWholeState() {
        // Declared as a reference slot it would publish one write for the
        // list's construction and nothing for any add or remove.
        assertEquals(SharedStateEvidence.LOCATION_KIND_MAP_STATE,
                declaredKind(StableOwner.class, "java.util.List", "rows"));
    }

    @Test
    public void aLazilyAllocatedListFieldKeepsItsReferenceCarrier() {
        // What changes when this field is assigned is WHICH list it names,
        // and a state carrier cannot say that.  At the access that would
        // select it the field is still null, so there is no container to
        // carry - the reference is the thing readers share.
        assertEquals("DECLARED_FIELD",
                declaredKind(LazyOwner.class, "java.util.List", "rows"));
    }

    @Test
    public void aMapFieldKeepsTodaysRuleWhicheverWayItIsDeclared() {
        // Admitting indexed containers must not change which map fields are
        // carried whole, so the associative rule stays unconditional.
        assertEquals(SharedStateEvidence.LOCATION_KIND_MAP_STATE,
                declaredKind(StableOwner.class, "java.util.Map", "entries"));
        assertEquals(SharedStateEvidence.LOCATION_KIND_MAP_STATE,
                declaredKind(LazyOwner.class, "java.util.Map", "entries"));
    }

    @Test
    public void anUnresolvableOwnerKeepsItsReferenceCarrier() {
        // Conservative: keeping the carrier the field already had loses
        // nothing, while carrying a mutable reference whole would lose every
        // writer of it.
        assertEquals("DECLARED_FIELD", kindOf(port(
                "<example.Absent: java.util.List rows>")));
        assertFalse(SharedFieldFlow.referenceStableField(
                "example.Absent", "rows"));
        assertFalse(SharedFieldFlow.referenceStableField("", "rows"));
        assertFalse(SharedFieldFlow.referenceStableField(
                StableOwner.class.getName(), "absent"));
    }

    @Test
    public void anArrayFieldKeepsItsElementAddressing() {
        // An array's elements already have their own locations; selecting the
        // array whole would name the same storage twice.
        Map<String, Map<String, Object>> carriers = new LinkedHashMap<>();
        Map<String, Object> keys = port("<example.State: int[] keys>");
        keys.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        RuntimeRegionPlanner.addAccessOwnedCarriers(carriers, keys, keys);
        assertTrue(carriers.keySet().toString(), carriers.containsKey(
                "DECLARED_FIELD\nexample.State#keys:[I"));
    }

    @Test
    public void theFinalityRuleSeparatesTheTwoRealFieldShapes() {
        assertTrue(SharedFieldFlow.referenceStableField(
                StableOwner.class.getName(), "rows"));
        assertFalse(SharedFieldFlow.referenceStableField(
                LazyOwner.class.getName(), "rows"));
        assertTrue(SharedFieldFlow.wholeStateCarrierField(
                StableOwner.class.getName(), "rows", "java.util.List"));
        assertFalse(SharedFieldFlow.wholeStateCarrierField(
                LazyOwner.class.getName(), "rows", "java.util.List"));
        // A set is versioned whole by no carrier, final or not.
        assertFalse(SharedFieldFlow.wholeStateCarrierField(
                StableOwner.class.getName(), "rows", "java.util.HashSet"));
    }

    @Test
    public void aFieldIsNeverBothAWholeStateAndAReferenceSlot() {
        String field = "<example.State: java.util.List rows>";
        List<SharedStateCapture.SharedCarrierRequest> conflicting =
                Arrays.asList(
                        request(SharedStateEvidence.LOCATION_KIND_MAP_STATE),
                        request("INSTANCE_FIELD"));
        assertTrue(SharedStateCapture.wholeStateAndPointerCarrier(
                conflicting, field));

        assertFalse(SharedStateCapture.wholeStateAndPointerCarrier(
                Collections.singletonList(request(
                        SharedStateEvidence.LOCATION_KIND_MAP_STATE)),
                field));
        assertFalse(SharedStateCapture.wholeStateAndPointerCarrier(
                Collections.singletonList(request("INSTANCE_FIELD")), field));
        assertFalse(SharedStateCapture.wholeStateAndPointerCarrier(
                new ArrayList<SharedStateCapture.SharedCarrierRequest>(),
                field));
        // A different field never conflicts with this one.
        assertFalse(SharedStateCapture.wholeStateAndPointerCarrier(
                conflicting, "<example.State: java.util.List other>"));
    }

    private static String declaredKind(Class<?> owner, String type,
                                       String name) {
        return kindOf(port("<" + owner.getName() + ": " + type + " " + name
                + ">"));
    }

    private static String kindOf(Map<String, Object> declaration) {
        Map<String, Map<String, Object>> carriers = new LinkedHashMap<>();
        declaration.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        RuntimeRegionPlanner.addAccessOwnedCarriers(
                carriers, declaration, declaration);
        assertEquals("one carrier per declaration", 1, carriers.size());
        return (String) carriers.values().iterator().next().get("kind");
    }

    private static SharedStateCapture.SharedCarrierRequest request(
            String kind) {
        JsonObject declaration = new JsonObject();
        declaration.addProperty("kind", kind);
        declaration.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
        declaration.addProperty("declaringClass", "example.State");
        declaration.addProperty("fieldName", "rows");
        declaration.addProperty("descriptor", "Ljava/util/List;");
        return new SharedStateCapture.SharedCarrierRequest(
                declaration, true);
    }

    private static Map<String, Object> port(String declaration) {
        Map<String, Object> port = new LinkedHashMap<>();
        port.put("fieldPathDeclarations",
                Collections.singletonList(declaration));
        port.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
        return port;
    }
}
