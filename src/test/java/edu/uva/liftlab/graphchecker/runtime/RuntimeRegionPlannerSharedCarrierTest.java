package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.contract.DependencyRole;
import org.junit.Test;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RuntimeRegionPlannerSharedCarrierTest {
    @Test
    public void declarationsFollowFinalRuntimeSemanticRole() {
        Map<String, Map<String, Object>> carriers = new LinkedHashMap<>();

        Map<String, Object> routingMap = port(
                "<example.Router: java.util.Map map>");
        RuntimeRegionPlanner.addAccessOwnedCarriers(
                carriers, routingMap, routingMap);
        assertTrue("a broad static frontier is not a semantic map value",
                carriers.isEmpty());

        Map<String, Object> concreteAccess = new LinkedHashMap<>();
        concreteAccess.put("dependencyRole",
                DependencyRole.CONCRETE_STRUCTURE_CARRIER);
        RuntimeRegionPlanner.addAccessOwnedCarriers(
                carriers, routingMap, concreteAccess);
        assertTrue("a routing map is replay structure", carriers.isEmpty());

        Map<String, Object> boundedMap = port(
                "<example.State: java.util.Map entries>");
        boundedMap.put("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        RuntimeRegionPlanner.addAccessOwnedCarriers(
                carriers, boundedMap, boundedMap);
        assertEquals(SharedStateEvidence.LOCATION_KIND_MAP_STATE,
                carriers.get("MAP_STATE\nexample.State#entries:Ljava/util/Map;")
                        .get("kind"));

        Map<String, Object> primitive = port(
                "<example.State: int epoch>");
        RuntimeRegionPlanner.addAccessOwnedCarriers(
                carriers, primitive, primitive);
        assertTrue(carriers.containsKey(
                "DECLARED_FIELD\nexample.State#epoch:I"));

        Map<String, Object> string = port(
                "<example.State: java.lang.String name>");
        RuntimeRegionPlanner.addAccessOwnedCarriers(
                carriers, string, string);
        assertTrue(carriers.containsKey(
                "DECLARED_FIELD\nexample.State#name:Ljava/lang/String;"));

        Map<String, Object> atomic = port(
                "<example.State: java.util.concurrent.atomic.AtomicInteger count>");
        atomic.put("mutatorDeclaredCallee",
                "<java.util.concurrent.atomic.AtomicInteger: int incrementAndGet()>");
        RuntimeRegionPlanner.addAccessOwnedCarriers(
                carriers, atomic, atomic);
        assertTrue(carriers.containsKey("DECLARED_FIELD\n"
                + "java.util.concurrent.atomic.AtomicInteger#value:I"));
        assertFalse("the Atomic wrapper remains replay structure",
                carriers.containsKey("DECLARED_FIELD\nexample.State#count:"
                        + "Ljava/util/concurrent/atomic/AtomicInteger;"));
    }

    private static Map<String, Object> port(String declaration) {
        Map<String, Object> port = new LinkedHashMap<>();
        port.put("fieldPathDeclarations",
                Collections.singletonList(declaration));
        // Static discovery can only conservatively call this a frontier.
        port.put("dependencyRole", DependencyRole.VALUE_FRONTIER);
        return port;
    }
}
