package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.VmExpressionIr;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import org.junit.Test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

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
