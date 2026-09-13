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
    public void aReadFromOverAConstantCarriesNoSymbolicValue() {
        assertTrue("the loose rule sees the wrapper",
                VmExpressionIr.carriesPropagatedValue(readFromConstant()));
        assertFalse("the strict rule looks inside it",
                VmExpressionIr.carriesSymbolicValue(readFromConstant()));
    }

    @Test
    public void aReadFromOverASymbolCarriesSymbolicValueEitherWay() {
        assertTrue(VmExpressionIr.carriesPropagatedValue(readFromSymbol()));
        assertTrue(VmExpressionIr.carriesSymbolicValue(readFromSymbol()));
    }

    @Test
    public void aDeclaredPrimitiveSourceMintsOverAConstant() {
        assertFalse("nothing is retained, so the caller mints",
                ConcolicRegionRuntime.carriesInputAuthority(
                        action("int", true), readFromConstant()));
    }

    @Test
    public void anUndeclaredPrimitiveSourceStillReusesTheCarrier() {
        assertTrue("unchanged for every automatic candidate",
                ConcolicRegionRuntime.carriesInputAuthority(
                        action("int", false), readFromConstant()));
    }

    /** keyId and expiryDate: declared, but reached by a real symbol. */
    @Test
    public void aDeclaredSourceReachedByASymbolIsStillPropagated() {
        assertTrue("the mint happened upstream; this read flows",
                ConcolicRegionRuntime.carriesInputAuthority(
                        action("int", true), readFromSymbol()));
    }

    /** There is no root to mint for a map, so the loose rule keeps it. */
    @Test
    public void aDeclaredContainerSourceKeepsTheLooseRule() {
        assertTrue(ConcolicRegionRuntime.carriesInputAuthority(
                action("java.util.Map", true), readFromConstant()));
    }

    @Test
    public void aConsumerBoundaryOverAConstantAlsoMintsWhenDeclared() {
        JsonObject boundary = new JsonObject();
        boundary.addProperty("_type", "ConsumerBoundaryExpression");
        boundary.addProperty("_kind", "FIELD_READ");
        boundary.add("expression", constant());
        assertTrue(VmExpressionIr.carriesPropagatedValue(boundary));
        assertFalse(VmExpressionIr.carriesSymbolicValue(boundary));
        assertFalse(ConcolicRegionRuntime.carriesInputAuthority(
                action("long", true), boundary));
    }

    /**
     * The {@code CausynthSymbolicSource} hook path asks the same question.
     *
     * <p>HDFS-17899 declares {@code BlockTokenSecretManager.serialNo} through
     * the Java hook rather than a plan action.  By the time
     * {@code updateKeys()} calls {@code symbolize(...)}, an earlier
     * activation has already installed a shared-state carrier on the field,
     * so the value arrives as a {@code ReadFrom} over the constant chain the
     * increment built.  Under the loose rule the hook reported {@code reused}
     * every time: no {@code sym__HDFS_BLOCK_KEY_SERIAL_NO__*} root, no
     * {@code CONFIGURED_SYMBOLIC_SOURCE_FIELD} evidence row, and an empty
     * {@code configuredSourceMaterializations} in the composed formula.</p>
     */
    @Test
    public void theHookMintsOverACarrierWrappedConstant() {
        assertFalse("a carrier-wrapped constant is not the hook's authority",
                ConcolicRegionRuntime.configuredSourceCarriesAuthority(
                        readFromConstant()));
    }

    @Test
    public void theHookStillDefersToARealUpstreamSymbol() {
        assertTrue("a root minted upstream flows through this read",
                ConcolicRegionRuntime.configuredSourceCarriesAuthority(
                        readFromSymbol()));
    }

    /** The exact serialNo shape: (ReadFrom + 1) % ReadFrom + ReadFrom. */
    @Test
    public void theHookMintsOverAnArithmeticChainOfCarrierReads() {
        JsonObject increment = binary("+", readFromConstant(), constant());
        JsonObject wrapped = binary("%", increment, readFromConstant());
        JsonObject chain = binary("+", wrapped, readFromConstant());
        assertTrue("the loose rule sees three wrappers",
                VmExpressionIr.carriesPropagatedValue(chain));
        assertFalse("but no symbol is inside any of them",
                ConcolicRegionRuntime.configuredSourceCarriesAuthority(chain));
    }

    @Test
    public void theHookDefersWhenOneLeafOfTheChainIsSymbolic() {
        JsonObject chain = binary("+",
                binary("%", readFromConstant(), readFromSymbol()),
                constant());
        assertTrue(ConcolicRegionRuntime.configuredSourceCarriesAuthority(
                chain));
    }

    @Test
    public void theHookReadsNothingAsNoAuthority() {
        assertFalse("an unsymbolized field answers \"no\"",
                ConcolicRegionRuntime.configuredSourceCarriesAuthority(null));
    }

    private static final String SERIAL_NO_PHASE =
            "SOURCE_PHASE.b6cff494-49b4-3843-afe6-6bc8564e0315";
    private static final String SERIAL_NO_SOURCE = "HDFS.BLOCK_KEY.SERIAL_NO";
    private static final String SERIAL_NO_OCCURRENCE = "hdfs-17899/nn0#epoch0"
            + "/region/REGION.aaa1cfd7-659b-3340-8d12-c81925e1de94#1#a1";
    private static final String SERIAL_NO_FIELD = "<org.apache.hadoop.hdfs"
            + ".security.token.block.BlockTokenSecretManager: int serialNo>";

    /**
     * What the hook read back after its mint on the first run that reached
     * it: the very chain above, unchanged.  The VM had kept the propagated
     * shadow, so the "mint" produced no symbol, and the evidence contract
     * has to refuse that read-back rather than let a carrier-wrapped
     * constant pose as a root.  The runtime line that files the refusal
     * names the shape, so the next diagnosis starts from the VM.
     */
    @Test
    public void aMintThatReadsBackTheCarrierTreeIsRefusedAsEvidence() {
        JsonObject chain = binary("+",
                binary("%", binary("+", readFromConstant(), constant()),
                        readFromConstant()),
                readFromConstant());
        try {
            SymbolicSourceEvidence.event(SERIAL_NO_PHASE, SERIAL_NO_SOURCE,
                    SERIAL_NO_OCCURRENCE, SERIAL_NO_FIELD, chain, 1, false,
                    "sym__" + SERIAL_NO_SOURCE + "__x__1");
            fail("a propagated tree is not a minted root");
        } catch (IllegalArgumentException refused) {
            assertTrue(refused.getMessage(), refused.getMessage()
                    .contains("must carry one non-constant VM symbol"));
        }
        assertEquals("BinaryExpression",
                ConcolicRegionRuntime.describeReadBack(chain));
        assertEquals("no expression",
                ConcolicRegionRuntime.describeReadBack(null));
    }

    /**
     * What the read-back is once the VM replaces the shadow: one
     * {@code FieldSymbolExp} carrying the phase's engine label, exactly as
     * HDFS-17960's {@code snapshotDeletionOrdered} mint reads back.
     */
    @Test
    public void aMintThatReadsBackOneVmSymbolIsEvidence() {
        String label = SymbolicSourceEvidence.engineLabelForPhase(
                SERIAL_NO_PHASE, SERIAL_NO_SOURCE);
        String raw = "M_I_field_" + label + "_org/apache/hadoop/hdfs/"
                + "security/token/block/BlockTokenSecretManager";
        JsonObject symbol = new JsonObject();
        symbol.addProperty("_type", "SymbolExpression");
        symbol.addProperty("_java_type", "I");
        symbol.addProperty("_exp", raw);
        String name = "sym__" + SERIAL_NO_SOURCE + "__"
                + SERIAL_NO_OCCURRENCE + "__1";
        JsonObject row = SymbolicSourceEvidence.event(SERIAL_NO_PHASE,
                SERIAL_NO_SOURCE, SERIAL_NO_OCCURRENCE, SERIAL_NO_FIELD,
                symbol, 1, false, name);
        assertEquals(SymbolicSourceEvidence.KIND,
                row.get("kind").getAsString());
        assertEquals(raw, row.get("rawSymbol").getAsString());
        assertEquals("I", row.get("javaType").getAsString());
        assertFalse(row.get(SymbolicSourceEvidence.REUSED).getAsBoolean());
        assertEquals(name, row.get(SymbolicSourceEvidence.SYMBOL)
                .getAsString());
        assertEquals("SymbolExpression " + raw,
                ConcolicRegionRuntime.describeReadBack(symbol));
        assertEquals("a mint that states no recorded value says nothing",
                "", SymbolicSourceEvidence.recordedValueOf(row));
        assertFalse(row.has(SymbolicSourceEvidence.RECORDED_VALUE));
    }

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

    /** Only a scalar the ledger can be compared against is spelled out. */
    @Test
    public void onlyScalarsAreSpelledAsRecordedValues() {
        assertEquals("false",
                ConcolicRegionRuntime.recordedScalar(Boolean.FALSE));
        assertEquals("7", ConcolicRegionRuntime.recordedScalar(7));
        assertEquals("-3", ConcolicRegionRuntime.recordedScalar(-3L));
        assertEquals("ordered",
                ConcolicRegionRuntime.recordedScalar("ordered"));
        assertEquals("a reference has no spelling a witness compares to",
                "", ConcolicRegionRuntime.recordedScalar(new Object()));
        assertEquals("", ConcolicRegionRuntime.recordedScalar(null));
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

    @Test
    public void anActionWithoutTheVerdictKeepsTheUnnarrowedBehaviour() {
        assertTrue("a plan with no selection file mints as it always did",
                action("int", false).mintEligible);
        assertTrue("and a declared root is mint-eligible by construction",
                action("int", true).mintEligible);
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
