package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.SymbolicSourceEvidence;
import edu.uva.liftlab.graphchecker.concolic.VmExpressionIr;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * A field the experiment declared must mint, even over a constant.
 *
 * <p>Once a shared-state carrier is installed, every later read of a field
 * arrives wrapped in a {@code ReadFrom} -- including a field only ever
 * written from constants.  The automatic rule reads that wrapper as "already
 * propagated" and skips the mint, which is why declaring a field symbolic
 * used to leave it concrete.  A declared primitive source asks the strict
 * question instead: is anything symbolic actually inside the tree?</p>
 */
public class DeclaredSymbolicRootMintTest {

    @Test
    public void aDeclaredPrimitiveSourceMintsOverAConstant() {
        assertFalse("nothing is retained, so the caller mints",
                ConcolicRegionRuntime.carriesInputAuthority(
                        action("int", true), readFromConstant()));
    }

    @Test
    public void theHookStillDefersToARealUpstreamSymbol() {
        assertTrue("a root minted upstream flows through this read",
                ConcolicRegionRuntime.configuredSourceCarriesAuthority(
                        readFromSymbol()));
    }

    private static final String SERIAL_NO_PHASE =
            "SOURCE_PHASE.b6cff494-49b4-3843-afe6-6bc8564e0315";
    private static final String SERIAL_NO_SOURCE = "HDFS.BLOCK_KEY.SERIAL_NO";
    private static final String SERIAL_NO_OCCURRENCE = "hdfs-17899/nn0#epoch0"
            + "/region/REGION.aaa1cfd7-659b-3340-8d12-c81925e1de94#1#a1";
    private static final String SERIAL_NO_FIELD = "<org.apache.hadoop.hdfs"
            + ".security.token.block.BlockTokenSecretManager: int serialNo>";

    /**
     * The concrete value the field held travels with the mint.
     *
     * <p>It exists only here: a configured source has no port and no
     * {@code symbolize} row, so the plan states nothing about it, and
     * dropping it at the mint leaves every downstream reader to default the
     * polarity. HDFS-17960's {@code snapshotDeletionOrdered} is recorded
     * {@code false} on the epoch-1 NameNode, and the default of {@code true}
     * reported a witness that reproduces the recorded failure as a flip of
     * it.</p>
     */
    @Test
    public void aMintCarriesTheValueTheFieldHeld() {
        String label = SymbolicSourceEvidence.engineLabelForPhase(
                ORDERED_PHASE, ORDERED_SOURCE);
        String raw = "M_Z_field_" + label + "_org/apache/hadoop/hdfs/server/"
                + "namenode/snapshot/SnapshotManager";
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "Z");
        symbol.addProperty("_exp", raw);

        JsonObject row = SymbolicSourceEvidence.event(ORDERED_PHASE,
                ORDERED_SOURCE, SERIAL_NO_OCCURRENCE, ORDERED_FIELD, symbol,
                1, false, "sym__ordered__1", "false");

        assertEquals("false", SymbolicSourceEvidence.recordedValueOf(row));
        assertEquals("false", row.get(SymbolicSourceEvidence.RECORDED_VALUE)
                .getAsString());
    }

    /**
     * A replay that overwrote the field before reading it states none.
     *
     * <p>The model assignment is written into the field before the mint
     * reads it back, so that activation observed the model's value. Calling
     * it "recorded" would publish a counterfactual as the recording, which
     * is the one way this row can be worse than absent.</p>
     */
    @Test
    public void aMintOverAModelAssignmentStatesNoRecordedValue() {
        String label = SymbolicSourceEvidence.engineLabelForPhase(
                ORDERED_PHASE, ORDERED_SOURCE);
        String raw = "M_Z_field_" + label + "_org/apache/hadoop/hdfs/server/"
                + "namenode/snapshot/SnapshotManager";
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "Z");
        symbol.addProperty("_exp", raw);

        JsonObject row = SymbolicSourceEvidence.event(ORDERED_PHASE,
                ORDERED_SOURCE, SERIAL_NO_OCCURRENCE, ORDERED_FIELD, symbol,
                1, false, "sym__ordered__1", null);

        assertFalse(row.has(SymbolicSourceEvidence.RECORDED_VALUE));
        assertEquals("", SymbolicSourceEvidence.recordedValueOf(row));
    }

    private static final String ORDERED_PHASE =
            "SOURCE_PHASE.f2395415-6c7d-3e1d-aa84-c9385b295a8c";
    private static final String ORDERED_SOURCE =
            "HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED";
    private static final String ORDERED_FIELD = "<org.apache.hadoop.hdfs"
            + ".server.namenode.snapshot.SnapshotManager:"
            + " boolean snapshotDeletionOrdered>";

    private static JsonObject binary(String op, JsonObject left,
                                     JsonObject right) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", "BinaryExpression");
        node.addProperty("_op", op);
        node.add("_left", left);
        node.add("_right", right);
        return node;
    }

    /**
     * A tracked carrier the plan did not make mint-eligible.
     *
     * <p>The scheduler now symbolizes every carrier so the VM keeps
     * publishing its candidates, and reserves the mint for the three
     * declaring authorities.  {@code mintEligible} is how that second
     * verdict reaches the replay, and it must default to the unnarrowed
     * behaviour when a plan row predates the field.</p>
     */
    @Test
    public void aTrackedCarrierIsNotMintEligible() {
        JsonObject json = new JsonObject();
        json.addProperty("symbol", "port.value");
        json.addProperty("javaType", "int");
        json.addProperty("mintEligible", false);
        assertFalse(new ConcolicRegionRuntime.SymbolizeAction(json)
                .mintEligible);
    }

    private static ConcolicRegionRuntime.SymbolizeAction action(
            String javaType, boolean declared) {
        JsonObject json = new JsonObject();
        json.addProperty("symbol", "port.serialNo");
        json.addProperty("javaType", javaType);
        json.addProperty("location", "RECEIVER_FIELD");
        json.addProperty("accessFieldSignature",
                "<org.apache.hadoop.hdfs.security.token.block"
                        + ".BlockTokenSecretManager: int serialNo>");
        if (declared) {
            json.addProperty(InputActionCatalog.DECLARED_SYMBOLIC_ROOT, true);
            json.addProperty("mintEligible", true);
        }
        return new ConcolicRegionRuntime.SymbolizeAction(json);
    }

    private static JsonObject constant() {
        JsonObject value = new JsonObject();
        value.addProperty("_type", "ConstExpr");
        value.addProperty("_exp", "Y_I_1771181829");
        return value;
    }

    /** The shape a carrier gives a field written only from constants. */
    private static JsonObject readFromConstant() {
        return readFrom(constant());
    }

    private static JsonObject readFromSymbol() {
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_exp", "M_I_REGION.aaa1cfd7");
        symbol.addProperty("_java_type", "int");
        return readFrom(symbol);
    }

    private static JsonObject readFrom(JsonObject candidateExpression) {
        JsonObject candidate = new JsonObject();
        candidate.addProperty("versionKind", "INITIAL");
        candidate.add("expression", candidateExpression);
        JsonArray candidates = new JsonArray();
        candidates.add(candidate);
        JsonObject read = new JsonObject();
        read.addProperty("_type", "ReadFromExpression");
        read.addProperty("authority", "VM_GUARDED_READ_FROM_V1");
        read.add("candidates", candidates);
        return read;
    }
}
