package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class ConfiguredSourceSelectorContractTest {
    private static final String SOURCE =
            "HDFS11741.NAMENODE.CURRENT_KEY_ID";
    private static final String FIELD =
            "<org.apache.hadoop.security.token.delegation.DelegationKey: "
                    + "int keyId>";
    private static final String DEPENDENT_SOURCE =
            "HDFS11741.NAMENODE.SELECTED_KEY_EXPIRY";
    private static final String CONSUME_A = "SOURCE_PHASE.consume-a";
    private static final String CONSUME_B = "SOURCE_PHASE.consume-b";
    private static final String PUBLISH_A = "SOURCE_PHASE.publish-a";
    private static final String PUBLISH_B = "SOURCE_PHASE.publish-b";
    private static final String OCCURRENCE =
            "cluster0/nn0/getBlockKeys#1";

    @Test
    public void exactOccurrenceRoundTripsWithoutSeedTaskIdOrValue() {
        JsonObject task = task(ConfiguredSourceSelectorContract.exactInt(
                CONSUME_A, PUBLISH_A, OCCURRENCE, SOURCE, FIELD));

        List<ConfiguredSourceSelectorContract.Selector> selectors =
                ConfiguredSourceSelectorContract.decode(task);

        assertEquals(1, selectors.size());
        assertEquals(OCCURRENCE,
                selectors.get(0).sourceOccurrenceId());
        assertEquals(CONSUME_A, selectors.get(0).consumePhaseId());
        assertEquals(PUBLISH_A, selectors.get(0).producerPhaseId());
        assertFalse(selectors.get(0).json().has("sourceTaskId"));
        assertFalse(selectors.get(0).json().has("recordedConcreteValue"));
    }

    @Test
    public void configDeclarationScopesSelectorToDependentSourceTasks() {
        JsonObject region = new JsonObject();
        JsonArray declarations = new JsonArray();
        declarations.add(ConfiguredSourceSelectorContract.intDeclaration(
                SOURCE, FIELD, Collections.singletonList(DEPENDENT_SOURCE)));
        region.add(ConfiguredSourceSelectorContract.CONFIG_FIELD,
                declarations);

        JsonObject decoded = ConfiguredSourceSelectorContract
                .declarationsOf(region).get(0);

        assertEquals(SOURCE, decoded.get("sourceId").getAsString());
        assertEquals(FIELD, decoded.get("fieldSignature").getAsString());
        assertEquals(ConfiguredSourceSelectorContract
                        .DECLARATION_SCHEMA_VERSION,
                decoded.get("schemaVersion").getAsInt());
        assertEquals(Collections.singletonList(DEPENDENT_SOURCE),
                ConfiguredSourceSelectorContract.requiredBySourceIds(
                        decoded));
        assertFalse(decoded.has("recordedConcreteValue"));
        assertFalse(decoded.has("sourceOccurrenceId"));
    }

    @Test
    public void configDeclarationFieldMustBeAnArrayWhenPresent() {
        JsonObject region = new JsonObject();
        region.addProperty(ConfiguredSourceSelectorContract.CONFIG_FIELD,
                "not-an-array");

        try {
            ConfiguredSourceSelectorContract.declarationsOf(region);
            fail("non-array configured source declarations must fail");
        } catch (IllegalArgumentException expected) {
            // Expected.
        }
    }

    @Test
    public void declarationRejectsMissingDuplicateOrMalformedTaskDemand() {
        expectDeclarationRejected(ConfiguredSourceSelectorContract
                .intDeclaration(SOURCE, FIELD,
                        Collections.singletonList(DEPENDENT_SOURCE)),
                declaration -> declaration.remove(
                        ConfiguredSourceSelectorContract
                                .REQUIRED_BY_SOURCE_IDS_FIELD));
        try {
            ConfiguredSourceSelectorContract.intDeclaration(SOURCE, FIELD,
                    Collections.<String>emptyList());
            fail("empty task-local demand must be rejected");
        } catch (IllegalArgumentException expected) {
            // Expected.
        }
        try {
            ConfiguredSourceSelectorContract.intDeclaration(SOURCE, FIELD,
                    Arrays.asList(DEPENDENT_SOURCE, DEPENDENT_SOURCE));
            fail("duplicate task-local demand must be rejected");
        } catch (IllegalArgumentException expected) {
            // Expected.
        }
    }

    @Test
    public void taskSelectorCarriesExactConsumeAndProducerPhases() {
        JsonObject selector = ConfiguredSourceSelectorContract.exactInt(
                CONSUME_A, PUBLISH_A, OCCURRENCE, SOURCE, FIELD);

        assertEquals(ConfiguredSourceSelectorContract.SCHEMA_VERSION,
                selector.get("schemaVersion").getAsInt());
        assertEquals("SESSION_EXACT_SOURCE_PHASE_VALUE_REQUIRED_V2",
                selector.get("authority").getAsString());
        assertEquals(CONSUME_A,
                selector.get("consumePhaseId").getAsString());
        assertEquals(PUBLISH_A,
                selector.get("producerPhaseId").getAsString());
        assertFalse(selector.has(ConfiguredSourceSelectorContract
                .REQUIRED_BY_SOURCE_IDS_FIELD));
    }

    @Test
    public void runtimeEvidenceNamesActualSessionProducerAndValue() {
        JsonObject selector = ConfiguredSourceSelectorContract.exactInt(
                CONSUME_A, PUBLISH_A, OCCURRENCE, SOURCE, FIELD);
        ConfiguredSourceSelectorContract.Selector decoded =
                ConfiguredSourceSelectorContract.decode(task(selector)).get(0);
        JsonObject owner = new JsonObject();
        JsonArray evidence = new JsonArray();
        String raw = ConfiguredSourceSelectorContract
                .expectedRawSymbolPrefix(
                        PUBLISH_A, SOURCE, FIELD)
                + "org/apache/hadoop/security/token/delegation/DelegationKey";
        evidence.add(ConfiguredSourceSelectorContract.evidence(decoded,
                "TASK.REPLAY.producer", raw, 17));
        owner.add(ConfiguredSourceSelectorContract.EVIDENCE_FIELD, evidence);

        JsonObject admitted = ConfiguredSourceSelectorContract
                .evidenceOf(owner).get(0);
        assertTrue(decoded.matches(admitted));
        assertEquals("TASK.REPLAY.producer",
                admitted.get("sourceTaskId").getAsString());
        assertEquals(17, admitted.get("selectedIntValue").getAsInt());
    }

    @Test
    public void duplicateSourceAuthorityIsRejected() {
        JsonObject selector = ConfiguredSourceSelectorContract.exactInt(
                CONSUME_A, PUBLISH_A, OCCURRENCE, SOURCE, FIELD);
        JsonObject task = task(selector);
        task.getAsJsonArray(ConfiguredSourceSelectorContract.TASK_FIELD)
                .add(selector.deepCopy());

        expectRejected(task);
    }

    @Test
    public void sameSourceMayBeConsumedTwiceWhenPhasesDiffer() {
        JsonObject task = task(ConfiguredSourceSelectorContract.exactInt(
                CONSUME_A, PUBLISH_A, OCCURRENCE, SOURCE, FIELD));
        task.getAsJsonArray(ConfiguredSourceSelectorContract.TASK_FIELD)
                .add(ConfiguredSourceSelectorContract.exactInt(
                        CONSUME_B, PUBLISH_B, OCCURRENCE, SOURCE, FIELD));

        List<ConfiguredSourceSelectorContract.Selector> selectors =
                ConfiguredSourceSelectorContract.decode(task);

        assertEquals(2, selectors.size());
        assertEquals(PUBLISH_A, selectors.get(0).producerPhaseId());
        assertEquals(PUBLISH_B, selectors.get(1).producerPhaseId());
    }

    @Test
    public void selectorTaskFieldMustBeAnArray() {
        JsonObject task = new JsonObject();
        task.addProperty(ConfiguredSourceSelectorContract.TASK_FIELD,
                "not-an-array");
        expectRejected(task);
    }

    @Test
    public void nonIntOrUntrustedAuthorityIsRejected() {
        JsonObject selector = ConfiguredSourceSelectorContract.exactInt(
                CONSUME_A, PUBLISH_A, OCCURRENCE, SOURCE, FIELD);
        selector.addProperty("fieldSignature",
                "<org.apache.hadoop.security.token.delegation."
                        + "DelegationKey: long expiryDate>");
        expectRejected(task(selector));

        selector = ConfiguredSourceSelectorContract.exactInt(
                CONSUME_A, PUBLISH_A, OCCURRENCE, SOURCE, FIELD);
        selector.addProperty("authority", "VALUE_MATCH_GUESS");
        expectRejected(task(selector));

        selector = ConfiguredSourceSelectorContract.exactInt(
                CONSUME_A, PUBLISH_A, OCCURRENCE, SOURCE, FIELD);
        selector.remove("producerPhaseId");
        expectRejected(task(selector));
    }

    private static JsonObject task(JsonObject selector) {
        JsonObject task = new JsonObject();
        JsonArray selectors = new JsonArray();
        selectors.add(selector);
        task.add(ConfiguredSourceSelectorContract.TASK_FIELD, selectors);
        return task;
    }

    private static void expectRejected(JsonObject task) {
        try {
            ConfiguredSourceSelectorContract.decode(task);
            fail("malformed selector must be rejected");
        } catch (IllegalArgumentException expected) {
            // Expected.
        }
    }

    private static void expectDeclarationRejected(
            JsonObject declaration, DeclarationMutation mutation) {
        JsonObject malformed = declaration.deepCopy();
        mutation.apply(malformed);
        JsonObject region = new JsonObject();
        JsonArray declarations = new JsonArray();
        declarations.add(malformed);
        region.add(ConfiguredSourceSelectorContract.CONFIG_FIELD,
                declarations);
        try {
            ConfiguredSourceSelectorContract.declarationsOf(region);
            fail("malformed declaration must be rejected");
        } catch (IllegalArgumentException expected) {
            // Expected.
        }
    }

    private interface DeclarationMutation {
        void apply(JsonObject declaration);
    }
}
