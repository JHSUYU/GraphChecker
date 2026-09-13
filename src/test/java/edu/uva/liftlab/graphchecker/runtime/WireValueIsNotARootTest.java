package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import org.junit.Test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A value the wire delivered is a carrier, never a root.
 *
 * <p>HDFS-17899 cuts the block-key export at
 * {@code PBHelper.convert(BlockKeyProto)}: the consumer reads
 * {@code getKeyId()} / {@code getExpiryDate()} off the received proto and
 * builds a {@code BlockKey} from them.  Those two reads are declared
 * {@code WIRE_FLOW} cut ports, so the expression that gives them meaning is
 * the NameNode's, installed by {@code attachCommunicationLeaf}.</p>
 *
 * <p>The attach runs <em>after</em> the materialization hook in the
 * instrumented frame -- both passes insert after the cut statement, so the
 * later pass lands closer to it -- which means nothing symbolic has reached
 * the local when the hook asks.  Treating that as "mint one" gives the
 * formula a free existential per port per consumer that the attach then
 * overwrites: four extra roots on the two DataNodes, a reach condition that
 * degenerates to {@code true}, and both fault valuations sat.  The reference
 * corpus never minted there -- it recorded the port as reused 57 times --
 * and only because a neighbouring accessor read happened to leave an
 * expression on the getter's return.  This pins the policy instead of the
 * luck.</p>
 */
public class WireValueIsNotARootTest {

    private static final String CONVERT =
            "<org.apache.hadoop.hdfs.protocolPB.PBHelper:"
                    + " org.apache.hadoop.hdfs.security.token.block.BlockKey"
                    + " convert(org.apache.hadoop.hdfs.protocol.proto"
                    + ".HdfsServerProtos$BlockKeyProto)>";
    private static final String KEY_ID_PORT =
            "XCH.1174244c.resp.block-key-id";
    private static final String EXPIRY_PORT =
            "XCH.cfba8c05.resp.block-key-expiry-date";

    @Test
    public void aPortStampedByTheFinalizerIsACutPort() {
        assertTrue(ConcolicRegionRuntime.declaredCommunicationCutPort(
                cutPort(KEY_ID_PORT, "int", true, false)));
    }

    /** A plan frozen by the build that wrote the verdict into the demand. */
    @Test
    public void theWrittenDemandAloneAlsoNamesACutPort() {
        assertTrue(ConcolicRegionRuntime.declaredCommunicationCutPort(
                cutPort(EXPIRY_PORT, "long", false, true)));
    }

    @Test
    public void anOrdinaryInputIsNotACutPort() {
        assertFalse(ConcolicRegionRuntime.declaredCommunicationCutPort(
                cutPort(EXPIRY_PORT, "long", false, false)));
        assertFalse("null is not a port",
                ConcolicRegionRuntime.declaredCommunicationCutPort(null));
    }

    /**
     * The mint the bug produced: the consumer's copy carried nothing yet.
     *
     * <p>{@code carriesInputAuthority} answering false is what sends the
     * caller towards {@code api.symbolizeField(fresh, "value", ...)}.  It
     * still answers false -- there really is nothing to reuse at that
     * instant -- so the refusal has to be the second half of the decision,
     * which is what {@code declaredCommunicationCutPort} supplies inside
     * {@code observeWithoutMinting}.</p>
     */
    @Test
    public void aCutPortWithNothingPropagatedStillRefusesToMint() {
        ConcolicRegionRuntime.SymbolizeAction port =
                cutPort(KEY_ID_PORT, "int", true, true);

        assertFalse("nothing has reached the local yet",
                ConcolicRegionRuntime.carriesInputAuthority(port, null));
        assertTrue("so the caller must leave it to the attach",
                ConcolicRegionRuntime.declaredCommunicationCutPort(port));
    }

    /**
     * Mint eligibility does not rescue the port, and cannot be relied on.
     *
     * <p>A plan the selection file narrowed already marks a cut port
     * {@code mintEligible: false}, so the carrier rule alone would cover
     * this case.  A campaign with no {@code symbolic-inputs.jsonl} -- and
     * every plan frozen before the field existed -- defaults the flag to
     * {@code true}, which is the state this asserts: the port must still
     * mint nothing.</p>
     */
    @Test
    public void aCutPortInAnUnnarrowedPlanIsStillNotAMintSite() {
        ConcolicRegionRuntime.SymbolizeAction port =
                cutPort(KEY_ID_PORT, "int", true, false);

        assertTrue("no selection file narrowed this plan", port.mintEligible);
        assertTrue("the port's own kind is what decides",
                ConcolicRegionRuntime.declaredCommunicationCutPort(port));
    }

    /** Once the attach has landed, the ordinary reuse path takes it. */
    @Test
    public void aCutPortReusesTheProducerExpression() {
        assertTrue(ConcolicRegionRuntime.carriesInputAuthority(
                cutPort(KEY_ID_PORT, "int", true, true), senderSymbol()));
    }

    /**
     * A cut port is never stamped a declared root, so the strict rule that
     * exists for a declared primitive source can never claim it.
     */
    @Test
    public void aCutPortIsNeverAlsoADeclaredRoot() {
        JsonObject json = portJson(EXPIRY_PORT, "long", true, true);
        assertFalse(json.has(InputActionCatalog.DECLARED_SYMBOLIC_ROOT));
    }

    private static ConcolicRegionRuntime.SymbolizeAction cutPort(
            String portId, String javaType, boolean stampedByFinalizer,
            boolean demandWritten) {
        return new ConcolicRegionRuntime.SymbolizeAction(portJson(
                portId, javaType, stampedByFinalizer, demandWritten));
    }

    private static JsonObject portJson(String portId, String javaType,
                                       boolean stampedByFinalizer,
                                       boolean demandWritten) {
        JsonObject json = new JsonObject();
        json.addProperty("symbol", portId);
        json.addProperty("portId", portId);
        json.addProperty("javaType", javaType);
        json.addProperty("location", "CALL_RETURN");
        json.addProperty("method", CONVERT);
        if (stampedByFinalizer) {
            json.addProperty("sourceKind", "COMMUNICATION_SITE_PORT");
        }
        if (demandWritten) {
            json.addProperty("symbolicDemand",
                    InputActionCatalog.DECLARED_COMMUNICATION_CUT_PORT);
        }
        return json;
    }

    /** What the attach installs: the producer's own symbol. */
    private static JsonObject senderSymbol() {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_exp", "M_I_REGION.aaa1cfd7");
        symbol.addProperty("_java_type", "int");
        return symbol;
    }
}
