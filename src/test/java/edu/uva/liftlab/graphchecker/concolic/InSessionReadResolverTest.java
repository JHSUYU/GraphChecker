package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Inside one replay a read has a value, not a choice.
 *
 * <p>Each test states one way the value is found: the write this session
 * made, the producer expression that arrived over a wire, the literal a
 * write before tracking left behind, and the refusal that keeps a cyclic
 * expression from being followed forever.</p>
 */
public class InSessionReadResolverTest {
    private static final String ROOT = "M_I_field_SRC.serialNo";

    /** A read of a location this session wrote takes that write's value. */
    @Test
    public void aReadTakesTheWriteThisSessionMade() {
        JsonObject row = row(versions("INSTANCE_FIELD", 9, 56,
                version(39, "INITIAL", constant(119981)),
                version(44, "WRITE", symbol(ROOT))));
        InSessionReadResolver resolver = InSessionReadResolver.of(
                Collections.singletonList(row));

        JsonElement resolved = resolver.resolve(read("INSTANCE_FIELD", 9, 56,
                46, candidate(39, "INITIAL", constant(119981)),
                candidate(44, "WRITE", symbol(ROOT))));

        assertEquals("SymbolExpression",
                resolved.getAsJsonObject().get("_type").getAsString());
        assertEquals(ROOT, resolved.getAsJsonObject().get("_exp")
                .getAsString());
        assertFalse(InSessionReadResolver.unresolved(resolved));
        assertFalse("a write this session made is not an INITIAL leaf",
                resolved.getAsJsonObject().has(
                        InSessionReadResolver.INITIAL_TAG));
    }

    /** The latest retained version is the one the program read. */
    @Test
    public void theLatestRetainedVersionIsTheOneRead() {
        JsonArray candidates = new JsonArray();
        candidates.add(candidate(39, "INITIAL", constant(1)));
        candidates.add(candidate(44, "WRITE", constant(2)));
        candidates.add(candidate(41, "WRITE", constant(3)));
        assertEquals(44L, InSessionReadResolver.observedVersion(candidates));
        assertEquals(-1L, InSessionReadResolver.observedVersion(
                new JsonArray()));
    }

    /** A value that arrived over a wire resolves to the producer's own. */
    @Test
    public void aWireArrivalResolvesToTheProducerExpression() {
        JsonObject consumer = row(versions("INSTANCE_FIELD", 31, 32,
                version(142, "INITIAL", constant(119982))));
        consumer.add("vmHandoffEvents", handoffs(handoff(144,
                symbol(ROOT))));
        InSessionReadResolver resolver = InSessionReadResolver.of(
                Arrays.asList(consumer));

        // What the consumer holds is its own literal read; what the wire
        // carried is the producer's expression, and that is the value.
        JsonElement resolved = resolver.resolve(boundary("RPC_ATTACH", 144,
                read("INSTANCE_FIELD", 31, 32, 143,
                        candidate(142, "INITIAL", constant(119982)))));

        assertEquals(ROOT, resolved.getAsJsonObject().get("_exp")
                .getAsString());
    }

    /** A literal written before tracking stays a literal, and says so. */
    @Test
    public void aValueOlderThanTheRecordingStaysALiteralAndSaysSo() {
        JsonObject row = row(versions("INSTANCE_FIELD", 4, 32,
                version(14, "INITIAL", constant(119980))));
        InSessionReadResolver resolver = InSessionReadResolver.of(
                Collections.singletonList(row));

        JsonElement resolved = resolver.resolve(read("INSTANCE_FIELD", 4, 32,
                15, candidate(14, "INITIAL", constant(119980))));

        JsonObject leaf = resolved.getAsJsonObject();
        assertEquals("119980", leaf.get("_exp").getAsString());
        assertTrue("the recording did not watch this value being produced",
                leaf.get(InSessionReadResolver.INITIAL_TAG).getAsBoolean());
        assertFalse(InSessionReadResolver.unresolved(resolved));
    }

    /** A self-referential definition is refused, not followed. */
    @Test
    public void aCycleIsRefusedRatherThanFollowed() {
        JsonObject definition = new JsonObject();
        definition.addProperty("expressionAnchor", "EXPR.loop");
        definition.add("expression", reference("EXPR.loop"));
        JsonArray definitions = new JsonArray();
        definitions.add(definition);
        JsonObject table = new JsonObject();
        table.add("definitions", definitions);
        JsonObject row = new JsonObject();
        row.add("sharedExpressionTable", table);

        JsonElement resolved = InSessionReadResolver.of(
                Collections.singletonList(row)).resolve(
                reference("EXPR.loop"));

        assertTrue(InSessionReadResolver.unresolved(resolved));
        assertTrue(resolved.getAsJsonObject()
                .get(InSessionReadResolver.UNRESOLVED_REASON).getAsString()
                .startsWith("cycle through"));
    }

    /** A read of a version nothing published is refused, not guessed. */
    @Test
    public void aReadWithNoPublishedWriteIsRefused() {
        JsonElement resolved = InSessionReadResolver.of(
                Collections.<JsonObject>emptyList()).resolve(
                read("INSTANCE_FIELD", 9, 56, 46, bareCandidate(44)));

        assertTrue(InSessionReadResolver.unresolved(resolved));
    }

    // ---- fixtures -------------------------------------------------------

    private static JsonObject symbol(String name) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "SymbolExpression");
        node.addProperty("_exp", name);
        return node;
    }

    private static JsonObject constant(int value) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConstExpr");
        node.addProperty("_exp", String.valueOf(value));
        return node;
    }

    private static JsonObject reference(String anchor) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "SharedExpressionReference");
        node.addProperty("expressionAnchor", anchor);
        return node;
    }

    private static JsonObject boundary(String kind, long event,
                                       JsonObject inner) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ConsumerBoundaryExpression");
        node.addProperty("boundaryKind", kind);
        node.addProperty("eventId", event);
        node.add("expression", inner);
        return node;
    }

    private static JsonObject location(String kind, long rid, long slot) {
        JsonObject node = new JsonObject();
        node.addProperty("locationKind", kind);
        node.addProperty("ownerSymRid", rid);
        node.addProperty("slot", slot);
        return node;
    }

    private static JsonObject read(String kind, long rid, long slot,
                                   long event, JsonObject... candidates) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ReadFromExpression");
        node.addProperty("readEventId", event);
        node.add("location", location(kind, rid, slot));
        JsonArray rows = new JsonArray();
        for (JsonObject candidate : candidates) rows.add(candidate);
        node.add("candidates", rows);
        return node;
    }

    private static JsonObject candidate(long version, String kind,
                                        JsonObject expression) {
        JsonObject node = bareCandidate(version);
        node.addProperty("versionKind", kind);
        node.add("expression", expression);
        return node;
    }

    private static JsonObject bareCandidate(long version) {
        JsonObject node = new JsonObject();
        node.addProperty("fieldVersionId", version);
        return node;
    }

    private static JsonObject version(long id, String kind,
                                      JsonObject expression) {
        JsonObject node = new JsonObject();
        node.addProperty("fieldVersionId", id);
        node.addProperty("versionKind", kind);
        node.add("expression", expression);
        return node;
    }

    private static JsonArray versions(String kind, long rid, long slot,
                                      JsonObject... rows) {
        JsonArray versions = new JsonArray();
        for (JsonObject row : rows) versions.add(row);
        JsonObject envelope = new JsonObject();
        envelope.add("location", location(kind, rid, slot));
        envelope.add("versions", versions);
        JsonObject record = new JsonObject();
        record.add("envelope", envelope);
        JsonArray records = new JsonArray();
        records.add(record);
        return records;
    }

    private static JsonObject handoff(long attachEvent,
                                      JsonObject expression) {
        JsonObject node = new JsonObject();
        node.addProperty("attachEventId", attachEvent);
        node.add("expression", expression);
        return node;
    }

    private static JsonArray handoffs(JsonObject... rows) {
        JsonArray events = new JsonArray();
        for (JsonObject row : rows) events.add(row);
        return events;
    }

    private static JsonObject row(JsonArray sharedFieldVersions) {
        JsonObject node = new JsonObject();
        node.add("sharedFieldVersions", sharedFieldVersions);
        return node;
    }
}
