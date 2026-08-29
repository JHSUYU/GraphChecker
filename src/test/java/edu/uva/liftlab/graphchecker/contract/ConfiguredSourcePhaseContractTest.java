package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

public class ConfiguredSourcePhaseContractTest {
    private static final String METHOD = "<example.Keys: void rotate()>";
    private static final String FIELD = "<example.Key: int keyId>";

    @Test
    public void occurrenceCarriesStableExactPhaseAndCallAncestry() {
        JsonObject encoded = ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                "ROTATING.KEY", FIELD, METHOD, 7);
        ConfiguredSourcePhaseContract.Declaration declaration =
                ConfiguredSourcePhaseContract.declarationsOf(
                        rows(encoded)).get(0);

        JsonObject first = ConfiguredSourcePhaseContract.occurrence(
                declaration, "node/nn0#epoch1/region/REGION.KEYS#3",
                2, 101, 30, 91, "<example.Hook: void publish()>",
                Arrays.asList(30L, 20L, 10L));
        JsonObject repeated =
                ConfiguredSourcePhaseContract.occurrence(
                        declaration,
                        "node/nn0#epoch1/region/REGION.KEYS#3",
                        2, 201, 30, 191,
                        "<example.Hook: void publish()>",
                        Arrays.asList(30L, 20L, 10L));

        assertEquals(first.get("phaseId"), repeated.get("phaseId"));
        assertEquals("PUBLISH", first.get("phaseKind").getAsString());
        assertEquals("ROTATING.KEY", first.get("sourceId").getAsString());
        assertEquals(FIELD, first.get("fieldSignature").getAsString());
        assertEquals(METHOD + "#u7", first.get("siteId").getAsString());
        assertEquals(101L, first.get("eventSeq").getAsLong());
        assertEquals(30L, first.get("ownerCallId").getAsLong());
        assertEquals(91L, first.get("invocationId").getAsLong());
        assertEquals(Arrays.asList(30L, 20L, 10L),
                callIds(first.getAsJsonArray("enclosingCallIds")));
        ConfiguredSourcePhaseContract.Occurrence decoded =
                ConfiguredSourcePhaseContract.occurrencesOf(
                        rows(first)).get(0);
        assertEquals("PUBLISH", decoded.phase().name());
        assertEquals(first.get("phaseId").getAsString(), decoded.phaseId());
        assertEquals("ROTATING.KEY", decoded.sourceId());
        assertEquals(FIELD, decoded.fieldSignature());
        assertEquals(Arrays.asList(30L, 20L, 10L),
                decoded.enclosingCallIds());
    }

    @Test(expected = IllegalArgumentException.class)
    public void rejectsAncestryThatDoesNotStartAtHookOwner() {
        ConfiguredSourcePhaseContract.Declaration declaration =
                ConfiguredSourcePhaseContract.declarationsOf(rows(
                        ConfiguredSourcePhaseContract.declaration(
                                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                                "ROTATING.KEY", FIELD, METHOD, 3))).get(0);

        ConfiguredSourcePhaseContract.occurrence(declaration,
                "node/nn0#epoch1/region/REGION.KEYS#3", 1,
                10, 30, 41, "<example.Hook: int consume()>",
                Arrays.asList(20L, 10L));
    }

    @Test
    public void occurrencePhaseRowsAreCopiedIntoExecutionTask() {
        ConfiguredSourcePhaseContract.Declaration declaration =
                ConfiguredSourcePhaseContract.declarationsOf(rows(
                        ConfiguredSourcePhaseContract.declaration(
                                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                                "ROTATING.KEY", FIELD, METHOD, 7))).get(0);
        JsonObject occurrence =
                ConfiguredSourcePhaseContract.occurrence(declaration,
                        "test/source#epoch0/region/R#1", 1,
                        10, 30, 41, "<example.Hook: void publish()>",
                        Arrays.asList(30L, 20L));
        JsonObject plan = new JsonObject();
        plan.addProperty("sourceKey", "test/source#epoch0");
        plan.addProperty("occurrenceId",
                "test/source#epoch0/region/R#1");
        plan.addProperty("relationKey", "test/source/relation/R");
        plan.addProperty("regionId", "R");
        JsonArray phaseRows = rows(occurrence);
        plan.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phaseRows);
        JsonObject goalRow = new JsonObject();
        goalRow.addProperty("goalId", "GOAL.1");
        goalRow.addProperty("kind", "TARGET_REACH_CLOSURE");
        goalRow.add("runtimeDefinitionMethods", new JsonArray());
        goalRow.add("symbolize", new JsonArray());
        goalRow.add("branches", new JsonArray());
        goalRow.add("edgeBindings", new JsonArray());
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "READY");
        goalRow.add("admission", admission);
        JsonArray goals = new JsonArray();
        goals.add(goalRow);
        plan.add("closureGoals", goals);

        RegionInstancePlan.Goal goal = RegionInstancePlan.decode(plan)
                .goals().get(0);
        ExecutionTask task = ExecutionTask.create(goal, "TASK.1",
                new JsonArray(), new JsonArray(), new JsonArray(),
                LoopBoundPolicy.cfgBackedges(
                        LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS), true, null);

        assertEquals(phaseRows,
                task.json().getAsJsonArray(
                        ConfiguredSourcePhaseContract.PLAN_FIELD));

        JsonArray foreignRows = rows(
                ConfiguredSourcePhaseContract.occurrence(declaration,
                        "test/source#epoch0/region/R#2", 1,
                        10, 30, 41, "<example.Hook: void publish()>",
                        Arrays.asList(30L, 20L)));
        JsonObject foreignPlan = plan.deepCopy();
        foreignPlan.add(ConfiguredSourcePhaseContract.PLAN_FIELD,
                foreignRows);
        try {
            RegionInstancePlan.decode(foreignPlan);
            fail("foreign source occurrence must be rejected");
        } catch (IllegalArgumentException expected) {
            assertEquals(true, expected.getMessage().contains(
                    "another occurrence"));
        }
    }

    @Test
    public void completePlanRequiresContiguousSiteOrdinals() {
        ConfiguredSourcePhaseContract.Declaration declaration = declaration();
        JsonObject first = occurrence(declaration, 1, 10, 41);
        JsonObject third = occurrence(declaration, 3, 30, 43);

        // A task may intentionally retain only selected phases from the full
        // occurrence, so its strict subsequence need not start at one.
        assertEquals(1, ConfiguredSourcePhaseContract.occurrencesOf(
                rows(third), false).size());
        try {
            ConfiguredSourcePhaseContract.occurrencesOf(
                    rows(first, third), true);
            fail("a complete occurrence may not skip a site ordinal");
        } catch (IllegalArgumentException expected) {
            assertEquals(true, expected.getMessage().contains(
                    "missing site ordinal"));
        }
    }

    @Test
    public void phaseLedgerRejectsDuplicateOrReorderedRuntimeIdentity() {
        ConfiguredSourcePhaseContract.Declaration declaration = declaration();
        JsonObject first = occurrence(declaration, 1, 10, 41);
        JsonObject duplicate = occurrence(declaration, 1, 20, 42);
        JsonObject second = occurrence(declaration, 2, 20, 42);

        try {
            ConfiguredSourcePhaseContract.occurrencesOf(
                    rows(first, duplicate), false);
            fail("one phase id may not occur twice");
        } catch (IllegalArgumentException expected) {
            assertEquals(true, expected.getMessage().contains(
                    "unique identities"));
        }
        try {
            ConfiguredSourcePhaseContract.occurrencesOf(
                    rows(second, first), false);
            fail("runtime event order may not be reversed");
        } catch (IllegalArgumentException expected) {
            assertEquals(true, expected.getMessage().contains(
                    "event order"));
        }
    }

    @Test
    public void declarationRequiresTheExactCurrentSchema() {
        JsonObject current = ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                "ROTATING.KEY", FIELD, METHOD, 7);
        for (String field : Arrays.asList(
                "schemaVersion", "kind", "authority", "siteId")) {
            JsonObject malformed = current.deepCopy();
            malformed.remove(field);
            try {
                ConfiguredSourcePhaseContract.declarationsOf(rows(malformed));
                fail("missing declaration field must be rejected: " + field);
            } catch (IllegalArgumentException expected) {
                assertEquals(true, expected.getMessage().contains(
                        "unsupported schema"));
            }
        }
        JsonObject stringVersion = current.deepCopy();
        stringVersion.addProperty("schemaVersion", "1");
        try {
            ConfiguredSourcePhaseContract.declarationsOf(rows(stringVersion));
            fail("string schemaVersion must be rejected");
        } catch (IllegalArgumentException expected) {
            assertEquals(true, expected.getMessage().contains(
                    "unsupported schema"));
        }
    }

    @Test
    public void occurrenceRequiresTheExactCurrentSchema() {
        JsonObject current = occurrence(declaration(), 1, 10, 41);
        for (String field : Arrays.asList(
                "schemaVersion", "kind", "authority", "siteId",
                "phaseKind", "ownerCallId")) {
            JsonObject malformed = current.deepCopy();
            malformed.remove(field);
            try {
                ConfiguredSourcePhaseContract.occurrencesOf(rows(malformed));
                fail("missing occurrence field must be rejected: " + field);
            } catch (IllegalArgumentException expected) {
                assertEquals(true, expected.getMessage().contains(
                        "unsupported schema"));
            }
        }
    }

    /** The one wire form a phase catalog is decoded from. */
    private static JsonArray rows(JsonObject... phases) {
        JsonArray encoded = new JsonArray();
        for (JsonObject phase : phases) encoded.add(phase);
        return encoded;
    }

    private static java.util.List<Long> callIds(JsonArray encoded) {
        java.util.List<Long> result = new java.util.ArrayList<>();
        for (com.google.gson.JsonElement value : encoded) {
            result.add(value.getAsLong());
        }
        return result;
    }

    private static ConfiguredSourcePhaseContract.Declaration declaration() {
        return ConfiguredSourcePhaseContract.declarationsOf(rows(
                ConfiguredSourcePhaseContract.declaration(
                        ConfiguredSourcePhaseContract.Phase.PUBLISH,
                        "ROTATING.KEY", FIELD, METHOD, 7))).get(0);
    }

    private static JsonObject occurrence(
            ConfiguredSourcePhaseContract.Declaration declaration,
            int ordinal, long eventSeq, long invocationId) {
        return ConfiguredSourcePhaseContract.occurrence(declaration,
                "node/nn0#epoch1/region/REGION.KEYS#3", ordinal,
                eventSeq, 30, invocationId,
                "<example.Hook: void publish()>",
                Arrays.asList(30L, 20L, 10L));
    }
}
