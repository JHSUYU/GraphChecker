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

    /**
     * A value that arrived over a wire resolves to the producer's own.
     *
     * <p>The VM substituted the sender's term into the boundary when the
     * value arrived, so the boundary's inner expression already names the
     * <em>producer's</em> location in the producer's numbering -- here the
     * NameNode's key field, whose write this replay also published.  The
     * matching {@code vmHandoffEvents} row records that the hop happened
     * and who produced it; it points back at this same boundary rather than
     * carrying a second expression, which is why following it instead would
     * re-enter the node and refuse a determined value.</p>
     */
    @Test
    public void aWireArrivalResolvesToTheHandoffVariable() {
        // The producer's side of the wire: the NameNode wrote the key id.
        JsonObject producer = row(versions("INSTANCE_FIELD", 24, 32,
                version(81, "WRITE", symbol(ROOT))));
        JsonObject consumer = row(versions("INSTANCE_FIELD", 91, 32,
                version(195, "INITIAL", constant(0))));
        consumer.add("vmHandoffEvents", handoffs(handoff(193,
                boundary("RPC_ATTACH", 193, null))));
        InSessionReadResolver resolver = InSessionReadResolver.of(
                Arrays.asList(producer, consumer));

        JsonElement resolved = resolver.resolve(boundary("RPC_ATTACH", 193,
                read("INSTANCE_FIELD", 24, 32, 192,
                        candidate(81, "WRITE", symbol(ROOT)))));

        // The value that arrived is free in this replay's formula.  Which
        // producer path delivered it, and under what conditions, is joined
        // to it once at the handoff, by the composer -- not inlined here,
        // where it would make a consumer flip need a producer replay.
        assertEquals(HANDOFF, resolved.getAsJsonObject().get("_exp")
                .getAsString());
        assertFalse("a hop is not a cycle",
                InSessionReadResolver.unresolved(resolved));
    }

    /**
     * A handoff row that points back at its own boundary is not a cycle.
     *
     * <p>It cannot be one any more: the boundary answers with the variable
     * its row mints and follows nothing.  The shape is kept because bug3
     * records it, and a reader that started following the row again would
     * re-enter this node.</p>
     */
    @Test
    public void aHandoffPointingAtItsOwnBoundaryIsNotACycle() {
        JsonObject producer = row(versions("INSTANCE_FIELD", 24, 32,
                version(81, "WRITE", symbol(ROOT))));
        JsonObject consumer = new JsonObject();
        // Exactly the shape hdfs-17899-bug3 records: the event's expression
        // is a reference to the anchor that defines the boundary itself.
        JsonObject inner = read("INSTANCE_FIELD", 24, 32, 192,
                candidate(81, "WRITE", symbol(ROOT)));
        JsonObject self = boundary("RPC_ATTACH", 193, inner);
        JsonObject definition = new JsonObject();
        definition.addProperty("expressionAnchor", "EXPR.attach");
        definition.add("expression", self);
        JsonArray definitions = new JsonArray();
        definitions.add(definition);
        JsonObject table = new JsonObject();
        table.add("definitions", definitions);
        consumer.add("sharedExpressionTable", table);
        consumer.add("vmHandoffEvents", handoffs(handoff(193,
                reference("EXPR.attach"))));

        JsonElement resolved = InSessionReadResolver.of(
                Arrays.asList(producer, consumer)).resolve(
                reference("EXPR.attach"));

        assertFalse(InSessionReadResolver.unresolved(resolved));
        assertEquals(HANDOFF, resolved.getAsJsonObject().get("_exp")
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

    /**
     * The changeover is over: the arm vocabulary is refused, not read.
     *
     * <p>While the VM was being changed this reader took either shape -- the
     * stated {@code observedVersion}, or the {@code candidates} array with
     * the newest of them taken as the one observed.  That second reading is
     * exactly the inference the design deletes, and the VM does not publish
     * the array any more, so a node carrying only it states no version and
     * is refused by name.</p>
     */
    @Test
    public void aReadCarryingOnlyTheOldCandidateArrayIsRefused() {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ReadFromExpression");
        node.addProperty("readEventId", 46);
        node.add("location", location("INSTANCE_FIELD", 9, 56));
        JsonArray candidates = new JsonArray();
        candidates.add(candidate(39, "INITIAL", constant(119981)));
        candidates.add(candidate(44, "WRITE", symbol(ROOT)));
        node.add("candidates", candidates);
        JsonObject row = row(versions("INSTANCE_FIELD", 9, 56,
                version(39, "INITIAL", constant(119981)),
                version(44, "WRITE", symbol(ROOT))));

        JsonElement resolved =
                InSessionReadResolver.of(Arrays.asList(row)).resolve(node);

        assertTrue(InSessionReadResolver.unresolved(resolved));
        String reason = resolved.getAsJsonObject()
                .get(InSessionReadResolver.UNRESOLVED_REASON).getAsString();
        assertTrue(reason,
                reason.contains(InSessionReadResolver.OBSERVED_VERSION));
    }

    /**
     * A key id crosses two objects and a wire, and lands on the root.
     *
     * <p>The shape hdfs-17899-bug3 records at the fatal read: the value the
     * DataNode received projects the sender's {@code DataEncryptionKey},
     * whose own field projects the imported {@code BlockKey}, whose own field
     * is the serial number the NameNode minted.  Three projections, one
     * replay, no arms -- each owner is a symbolic object reference, and each
     * reference plus offset names a location this replay published.</p>
     */
    @Test
    public void aProjectionThroughObjectReferencesReachesTheRoot() {
        JsonObject minted = row(versions("INSTANCE_FIELD", 17, 32,
                version(47, "INITIAL", constant(0)),
                version(48, "WRITE", symbol(ROOT))));
        JsonObject imported = row(versions("INSTANCE_FIELD", 159, 32,
                version(299, "INITIAL", constant(0)),
                version(300, "WRITE", projection(17, 32))));
        JsonObject sent = row(versions("INSTANCE_FIELD", 178, 32,
                version(342, "INITIAL", constant(0)),
                version(343, "WRITE", projection(159, 32))));
        InSessionReadResolver resolver = InSessionReadResolver.of(
                Arrays.asList(minted, imported, sent));

        JsonElement resolved = resolver.resolve(projection(178, 32));

        assertFalse(InSessionReadResolver.unresolved(resolved));
        assertEquals("SymbolExpression",
                resolved.getAsJsonObject().get("_type").getAsString());
        assertEquals(ROOT, resolved.getAsJsonObject().get("_exp")
                .getAsString());
    }

    /** A field this replay wrote twice does not say which write was seen. */
    @Test
    public void aProjectionOfATwiceWrittenFieldIsRefused() {
        JsonObject row = row(versions("INSTANCE_FIELD", 9, 56,
                version(39, "INITIAL", constant(0)),
                version(41, "WRITE", constant(119982)),
                version(44, "WRITE", symbol(ROOT))));

        JsonElement resolved = InSessionReadResolver.of(
                Collections.singletonList(row)).resolve(projection(9, 56));

        assertTrue(InSessionReadResolver.unresolved(resolved));
        assertTrue(resolved.getAsJsonObject()
                .get(InSessionReadResolver.UNRESOLVED_REASON).getAsString()
                .contains("written 2 times"));
    }

    /**
     * Three writes, and the access between the second and the third.
     *
     * <p>One execution has exactly one write of a location live at any
     * event, so the value this projection read is the write with the
     * greatest version id below the access.  Version ids and the decision's
     * event id come off one session counter, which is what makes them
     * comparable -- the branch marker's own per-thread sequence is not, and
     * comparing the two would put every decision before every write.</p>
     */
    @Test
    public void aProjectionTakesTheWriteLiveAtItsOwnEvent() {
        JsonObject row = row(versions("INSTANCE_FIELD", 9, 56,
                version(39, "INITIAL", constant(0)),
                version(41, "WRITE", constant(119981)),
                version(44, "WRITE", constant(119982)),
                version(47, "WRITE", symbol(ROOT))));

        JsonElement resolved = InSessionReadResolver.of(
                Collections.singletonList(row))
                .resolve(projection(9, 56), 45);

        assertFalse(InSessionReadResolver.unresolved(resolved));
        assertEquals("119982",
                resolved.getAsJsonObject().get("_exp").getAsString());
    }

    /** Every write is after the access, so what it read predates tracking. */
    @Test
    public void aProjectionBeforeEveryWriteReadsTheInitialVersion() {
        JsonObject row = row(versions("INSTANCE_FIELD", 9, 56,
                version(39, "INITIAL", constant(119980)),
                version(41, "WRITE", constant(119981)),
                version(44, "WRITE", symbol(ROOT))));

        JsonElement resolved = InSessionReadResolver.of(
                Collections.singletonList(row))
                .resolve(projection(9, 56), 40);

        assertFalse(InSessionReadResolver.unresolved(resolved));
        assertEquals("119980",
                resolved.getAsJsonObject().get("_exp").getAsString());
        assertTrue(resolved.getAsJsonObject()
                .get(InSessionReadResolver.INITIAL_TAG).getAsBoolean());
    }

    /** A node that states the version it observed needs no ordering at all. */
    @Test
    public void aProjectionStatingItsObservedVersionTakesIt() {
        JsonObject row = row(versions("INSTANCE_FIELD", 9, 56,
                version(41, "WRITE", constant(119981)),
                version(44, "WRITE", constant(119982)),
                version(47, "WRITE", symbol(ROOT))));
        JsonObject node = projection(9, 56);
        node.addProperty(InSessionReadResolver.OBSERVED_VERSION, 41);

        JsonElement resolved = InSessionReadResolver.of(
                Collections.singletonList(row)).resolve(node);

        assertFalse(InSessionReadResolver.unresolved(resolved));
        assertEquals("119981",
                resolved.getAsJsonObject().get("_exp").getAsString());
    }

    /** Neither the node nor the decision says: unstated, never guessed. */
    @Test
    public void aProjectionWithNoVersionAndNoClockIsRefused() {
        JsonObject row = row(versions("INSTANCE_FIELD", 9, 56,
                version(41, "WRITE", constant(119981)),
                version(44, "WRITE", symbol(ROOT))));

        JsonElement resolved = InSessionReadResolver.of(
                Collections.singletonList(row)).resolve(projection(9, 56));

        assertTrue(InSessionReadResolver.unresolved(resolved));
        String reason = resolved.getAsJsonObject()
                .get(InSessionReadResolver.UNRESOLVED_REASON).getAsString();
        assertTrue(reason, reason.contains("observedVersion"));
        assertTrue(reason, reason.contains("eventId"));
    }

    /** A projection over something that is not an object stays a projection. */
    @Test
    public void aProjectionOverANonReferenceIsLeftAlone() {
        assertEquals(-1L, InSessionReadResolver.referencedObject(
                symbol("M_I_field_SRC.serialNo")));
        assertEquals(-1L, InSessionReadResolver.referencedObject(
                constant(3)));
        assertEquals(159L, InSessionReadResolver.referencedObject(
                symbol("M_L'org/apache/hadoop/A'_159")));

        JsonObject over = new JsonObject();
        over.addProperty("_type", "FieldAccessExpression");
        over.addProperty("fieldOffset", 32);
        over.add("owner", constant(7));
        JsonElement resolved = InSessionReadResolver.of(
                Collections.<JsonObject>emptyList()).resolve(over);

        assertFalse(InSessionReadResolver.unresolved(resolved));
        assertEquals("FieldAccessExpression",
                resolved.getAsJsonObject().get("_type").getAsString());
    }

    // ---- fixtures -------------------------------------------------------

    private static JsonObject projection(long ownerRid, long offset) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "FieldAccessExpression");
        node.addProperty("ownerClass", "org/apache/hadoop/A");
        node.addProperty("fieldOffset", offset);
        node.add("owner", symbol("M_L'org/apache/hadoop/A'_" + ownerRid));
        return node;
    }

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

    /**
     * A read node that names the one version it observed.
     *
     * <p>The alternatives it did not take are not published any more, and
     * nothing here needs them: the read has a value, not a choice.</p>
     */
    @Test
    public void aReadNamesTheVersionItObservedAndNothingElse() {
        JsonObject row = row(versions("INSTANCE_FIELD", 9, 56,
                version(39, "INITIAL", constant(119981)),
                version(44, "WRITE", symbol(ROOT))));
        InSessionReadResolver resolver = InSessionReadResolver.of(
                Collections.singletonList(row));

        JsonElement resolved = resolver.resolve(
                observedRead("INSTANCE_FIELD", 9, 56, 46,
                        version(44, "WRITE", symbol(ROOT))));

        assertEquals(ROOT, resolved.getAsJsonObject().get("_exp")
                .getAsString());
        assertFalse(InSessionReadResolver.unresolved(resolved));
    }

    /** The observed version still says when nothing watched it produced. */
    @Test
    public void anObservedInitialVersionIsStillMarked() {
        JsonObject row = row(versions("INSTANCE_FIELD", 4, 32,
                version(14, "INITIAL", constant(119980))));
        InSessionReadResolver resolver = InSessionReadResolver.of(
                Collections.singletonList(row));

        JsonElement resolved = resolver.resolve(
                observedRead("INSTANCE_FIELD", 4, 32, 15,
                        version(14, "INITIAL", constant(119980))));

        assertTrue(resolved.getAsJsonObject()
                .get(InSessionReadResolver.INITIAL_TAG).getAsBoolean());
    }

    /** A read node carrying only the version it observed. */
    private static JsonObject observedRead(String kind, long rid, long slot,
                                           long event, JsonObject observed) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ReadFromExpression");
        node.addProperty("readEventId", event);
        node.add("location", location(kind, rid, slot));
        node.add(InSessionReadResolver.OBSERVED_VERSION, observed);
        return node;
    }

    /**
     * A read node: the location it read and the one version it observed.
     *
     * <p>It used to carry every version retained at the read and leave the
     * choice to a reader.  The VM states the one it saw, so these fixtures
     * state it too -- the last of the versions handed in, which is the one
     * the old newest-wins rule would have picked.</p>
     */
    private static JsonObject read(String kind, long rid, long slot,
                                   long event, JsonObject... observed) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "ReadFromExpression");
        node.addProperty("readEventId", event);
        node.add("location", location(kind, rid, slot));
        JsonObject newest = null;
        for (JsonObject candidate : observed) {
            if (newest == null || candidate.get("fieldVersionId").getAsLong()
                    > newest.get("fieldVersionId").getAsLong()) {
                newest = candidate;
            }
        }
        if (newest != null) {
            node.add(InSessionReadResolver.OBSERVED_VERSION, newest);
        }
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

    private static final String HANDOFF = "M_I_HOFF.key_java/lang/Integer";

    private static JsonObject handoff(long attachEvent,
                                      JsonObject expression) {
        JsonObject node = new JsonObject();
        node.addProperty("attachEventId", attachEvent);
        node.addProperty(InSessionReadResolver.HANDOFF_PHASE_ID,
                "HANDOFF_PHASE.key");
        node.addProperty(InSessionReadResolver.HANDOFF_SYMBOL, HANDOFF);
        node.addProperty("javaType", "I");
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
