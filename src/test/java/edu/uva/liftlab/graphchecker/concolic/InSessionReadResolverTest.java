package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Inside one replay a read has a value, not a choice.
 *
 * <p>Each rule states one way that value is found -- the write this
 * session made, the expression that arrived over a wire, the literal a write
 * before tracking left behind -- and, where the replay published none of
 * them, a refusal under its own name instead of a guess.</p>
 */
public class InSessionReadResolverTest {
    private static final String ROOT = "M_I_field_SRC.serialNo";
    private static final String HANDOFF = "M_I_HOFF.key_java/lang/Integer";

    /**
     * A read takes the value this replay published for the location it read.
     *
     * <p>The write this session made; the literal a write before tracking
     * left behind, tagged because the recording did not watch it being
     * produced; the write live at the reading event; and the projection chain
     * that walks symbolic object references back to the root.</p>
     */
    @Test
    public void aReadTakesTheValueThisReplayPublished() {
        check(ROOT, false, -1, read("INSTANCE_FIELD", 9, 56, 46,
                version(44, "WRITE", symbol(ROOT))),
                row("INSTANCE_FIELD", 9, 56,
                        version(39, "INITIAL", constant(119981)),
                        version(44, "WRITE", symbol(ROOT))));

        // A value older than the recording stays a literal, and says so.
        check("119980", true, -1, read("INSTANCE_FIELD", 4, 32, 15,
                version(14, "INITIAL", constant(119980))),
                row("INSTANCE_FIELD", 4, 32,
                        version(14, "INITIAL", constant(119980))));

        // hdfs-17899-bug3's fatal read: the value the DataNode received
        // projects the sender's key, whose field projects the imported one,
        // whose own field is the serial number the NameNode minted.
        check(ROOT, false, -1, projection(178, 32),
                row("INSTANCE_FIELD", 17, 32,
                        version(48, "WRITE", symbol(ROOT))),
                row("INSTANCE_FIELD", 159, 32,
                        version(300, "WRITE", projection(17, 32))),
                row("INSTANCE_FIELD", 178, 32,
                        version(343, "WRITE", projection(159, 32))));

        // The value a projection read is the write with the greatest
        // version id below the access -- both come off one session counter,
        // which is what makes them comparable.
        JsonObject thrice = row("INSTANCE_FIELD", 9, 56,
                version(39, "INITIAL", constant(119980)),
                version(41, "WRITE", constant(119981)),
                version(44, "WRITE", constant(119982)),
                version(47, "WRITE", symbol(ROOT)));
        check("119982", false, 45, projection(9, 56), thrice);
        check("119980", true, 40, projection(9, 56), thrice);
    }

    /**
     * A value that arrived over a wire is answered by its handoff variable.
     *
     * <p>It answers with the variable its row mints and follows nothing; a
     * row minting none is refused by name.</p>
     */
    @Test
    public void aWireArrivalIsAnsweredByTheHandoffThatMintedIt() {
        // The producer's side of the wire: the NameNode wrote the key id.
        JsonObject producer = row("INSTANCE_FIELD", 24, 32,
                version(81, "WRITE", symbol(ROOT)));
        JsonObject consumer = row("INSTANCE_FIELD", 91, 32,
                version(195, "INITIAL", constant(0)));
        JsonArray minted = new JsonArray();
        minted.add(handoff(193, boundary("RPC_ATTACH", 193, null)));
        consumer.add("vmHandoffEvents", minted);

        // The variable that row mints answers the read: a hop is not a cycle.
        check(HANDOFF, false, -1, arrival(), producer, consumer);

        JsonArray mintless = new JsonArray();
        mintless.add(json("{\"attachEventId\":193}"));
        consumer.add("vmHandoffEvents", mintless);

        refuses(Arrays.asList(producer, consumer), arrival(),
                InSessionReadResolver.HANDOFF_SYMBOL);
    }

    /**
     * What the replay did not publish is refused by name, never inferred.
     *
     * <p>A cycle is refused rather than followed; a version nothing
     * published is refused rather than guessed; a location this replay wrote
     * twice does not say which write the access saw; and a node stating no
     * {@link InSessionReadResolver#OBSERVED_VERSION} and no event to order
     * it by states no version at all.</p>
     */
    @Test
    public void anUnpublishedOrAmbiguousReadIsRefusedByName() {
        JsonObject cyclic = json("{\"sharedExpressionTable\":{\"definitions\""
                + ":[{\"expressionAnchor\":\"EXPR.loop\",\"expression\":"
                + "{\"_type\":\"SharedExpressionReference\","
                + "\"expressionAnchor\":\"EXPR.loop\"}}]}}");
        refuses(Collections.singletonList(cyclic),
                json("{\"_type\":\"SharedExpressionReference\","
                        + "\"expressionAnchor\":\"EXPR.loop\"}"),
                "cycle through");

        refuses(Collections.<JsonObject>emptyList(),
                read("INSTANCE_FIELD", 9, 56, 46,
                        json("{\"fieldVersionId\":44}")), "");

        refuses(Collections.singletonList(row("INSTANCE_FIELD", 9, 56,
                version(39, "INITIAL", constant(0)),
                version(41, "WRITE", constant(119982)),
                version(44, "WRITE", symbol(ROOT)))),
                projection(9, 56), "written 2 times");

        String unstated = refuses(Collections.singletonList(
                row("INSTANCE_FIELD", 9, 56,
                        version(41, "WRITE", constant(119981)),
                        version(44, "WRITE", symbol(ROOT)))),
                projection(9, 56), InSessionReadResolver.OBSERVED_VERSION);
        assertTrue(unstated, unstated.contains("eventId"));
    }

    private static void check(String expected, boolean initial, long clock,
                              JsonObject node, JsonObject... published) {
        List<JsonObject> rows = Arrays.asList(published);
        JsonElement resolved = clock < 0
                ? InSessionReadResolver.of(rows).resolve(node)
                : InSessionReadResolver.of(rows).resolve(node, clock);
        assertFalse(InSessionReadResolver.unresolved(resolved));
        JsonObject leaf = resolved.getAsJsonObject();
        assertEquals(expected, leaf.get("_exp").getAsString());
        assertEquals(initial, leaf.has(InSessionReadResolver.INITIAL_TAG));
    }

    private static String refuses(List<JsonObject> rows, JsonObject node,
                                  String named) {
        JsonElement resolved = InSessionReadResolver.of(rows).resolve(node);
        assertTrue("the resolver must not guess a value",
                InSessionReadResolver.unresolved(resolved));
        JsonObject refusal = resolved.getAsJsonObject();
        String reason = refusal.has(InSessionReadResolver.UNRESOLVED_REASON)
                ? refusal.get(InSessionReadResolver.UNRESOLVED_REASON)
                        .getAsString() : "";
        assertTrue(reason, reason.contains(named));
        return reason;
    }

    private static JsonObject arrival() {
        return boundary("RPC_ATTACH", 193, read("INSTANCE_FIELD", 24, 32,
                192, version(81, "WRITE", symbol(ROOT))));
    }

    private static JsonObject json(String json) {
        return JsonParser.parseString(json).getAsJsonObject();
    }

    private static JsonObject symbol(String name) {
        return json("{\"_type\":\"SymbolExpression\",\"_exp\":\""
                + name + "\"}");
    }

    private static JsonObject constant(int value) {
        return json("{\"_type\":\"ConstExpr\",\"_exp\":\"" + value + "\"}");
    }

    private static JsonObject projection(long ownerRid, long offset) {
        JsonObject node = json("{\"_type\":\"FieldAccessExpression\","
                + "\"ownerClass\":\"org/apache/hadoop/A\","
                + "\"fieldOffset\":" + offset + "}");
        node.add("owner", symbol("M_L'org/apache/hadoop/A'_" + ownerRid));
        return node;
    }

    private static JsonObject boundary(String kind, long event,
                                       JsonObject inner) {
        JsonObject node = json("{\"_type\":\"ConsumerBoundaryExpression\","
                + "\"boundaryKind\":\"" + kind + "\",\"eventId\":" + event
                + "}");
        node.add("expression", inner);
        return node;
    }

    private static JsonObject location(String kind, long rid, long slot) {
        return json("{\"locationKind\":\"" + kind + "\",\"ownerSymRid\":"
                + rid + ",\"slot\":" + slot + "}");
    }

    /** A read node: the location it read, and the version it observed. */
    private static JsonObject read(String kind, long rid, long slot,
                                   long event, JsonObject observed) {
        JsonObject node = json("{\"_type\":\"ReadFromExpression\","
                + "\"readEventId\":" + event + "}");
        node.add("location", location(kind, rid, slot));
        node.add(InSessionReadResolver.OBSERVED_VERSION, observed);
        return node;
    }

    private static JsonObject version(long id, String kind,
                                      JsonObject expression) {
        JsonObject node = json("{\"fieldVersionId\":" + id
                + ",\"versionKind\":\"" + kind + "\"}");
        node.add("expression", expression);
        return node;
    }

    private static JsonObject row(String kind, long rid, long slot,
                                  JsonObject... rows) {
        JsonObject published = json("{\"sharedFieldVersions\":"
                + "[{\"envelope\":{\"versions\":[]}}]}");
        JsonObject envelope = published.getAsJsonArray("sharedFieldVersions")
                .get(0).getAsJsonObject().getAsJsonObject("envelope");
        envelope.add("location", location(kind, rid, slot));
        for (JsonObject version : rows) {
            envelope.getAsJsonArray("versions").add(version);
        }
        return published;
    }

    private static JsonObject handoff(long attachEvent, JsonObject inner) {
        JsonObject node = json("{\"attachEventId\":" + attachEvent
                + ",\"" + InSessionReadResolver.HANDOFF_PHASE_ID
                + "\":\"HANDOFF_PHASE.key\",\""
                + InSessionReadResolver.HANDOFF_SYMBOL + "\":\"" + HANDOFF
                + "\",\"javaType\":\"I\"}");
        node.add("expression", inner);
        return node;
    }
}
