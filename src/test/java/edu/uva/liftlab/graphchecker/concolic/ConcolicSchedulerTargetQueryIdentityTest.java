package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;
import org.junit.Test;

import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/** Target-first aggregation requires one stable identity per branch query. */
public class ConcolicSchedulerTargetQueryIdentityTest {

    @Test
    public void twoTargetQueriesKeepDistinctNonemptyAggregationKeys()
            throws Exception {
        JsonObject first = query("TASK.SEED.A", "REGION.A");
        JsonObject second = query("TASK.SEED.B", "REGION.B");
        Map<String, JsonObject> indexed = new LinkedHashMap<>();

        ConcolicScheduler.indexTargetQuery(indexed, first);
        ConcolicScheduler.indexTargetQuery(indexed, second);

        assertFalse(first.get("queryKey").getAsString().isEmpty());
        assertFalse(second.get("queryKey").getAsString().isEmpty());
        assertFalse(first.get("queryKey").equals(second.get("queryKey")));
        assertEquals(2, indexed.size());
        assertTrue(indexed.containsKey(
                ConcolicScheduler.targetBranchQueryKey("TASK.SEED.A")));
        assertTrue(indexed.containsKey(
                ConcolicScheduler.targetBranchQueryKey("TASK.SEED.B")));
    }

    @Test
    public void missingQueryKeyIsRefusedAtTheTargetFirstAggregationBoundary()
            throws Exception {
        try {
            ConcolicScheduler.indexTargetQuery(new LinkedHashMap<>(),
                    new JsonObject());
            fail("a target query without queryKey must not be aggregated");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().contains(
                    "scheduled row has no queryKey"));
        }
    }

    @Test
    public void oneQueryKeyCannotNameTwoDifferentTargetQueries()
            throws Exception {
        JsonObject first = query("TASK.SEED.A", "REGION.A");
        JsonObject conflicting = query("TASK.SEED.A", "REGION.B");
        Map<String, JsonObject> indexed = new LinkedHashMap<>();
        ConcolicScheduler.indexTargetQuery(indexed, first);

        try {
            ConcolicScheduler.indexTargetQuery(indexed, conflicting);
            fail("one queryKey must not overwrite another target query");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().contains(
                    "conflicting scheduled queryKey"));
        }
    }

    private static JsonObject query(String seedTaskId, String regionId) {
        JsonObject query = new JsonObject();
        query.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        query.addProperty("queryKey",
                ConcolicScheduler.targetBranchQueryKey(seedTaskId));
        query.addProperty("regionId", regionId);
        return query;
    }
}
