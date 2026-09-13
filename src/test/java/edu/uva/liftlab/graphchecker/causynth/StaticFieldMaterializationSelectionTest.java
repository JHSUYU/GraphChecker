package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;
import soot.ArrayType;
import soot.BooleanType;
import soot.ByteType;
import soot.IntType;
import soot.Modifier;
import soot.Scene;
import soot.SootClass;
import soot.SootField;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A static field read is selected only in the one shape this pipeline can
 * materialize, and every other selected static read is refused by verdict.
 *
 * <p>Reproduces the HDFS-17960 INSTRUMENT[0] failure exactly.  Once
 * {@code ConcolicScheduler.decide} stopped concretizing undeclared carriers,
 * the plan kept an {@code ACTIVATION_FIELD_RECEIVER} action on
 * {@code FSDirectory.DOT_RESERVED} -- a {@code static final byte[]} constant
 * -- SYMBOLIC.  The shared-carrier branch already refused static
 * non-primitives, but the named-field-target fallback below it did not, so the
 * read was selected at <em>every</em> site naming that field and the
 * instrumenter threw {@code STATIC_FIELD_MATERIALIZATION_UNSUPPORTED} at a
 * site in a different method than the action's own.</p>
 */
public class StaticFieldMaterializationSelectionTest {
    /** The method whose read killed the campaign, not the action's own site. */
    private static final String FATAL_READER =
            "<example.FSDirectory: byte[][] resolveComponents(byte[][])>";
    private static final String ACTION_READER =
            "<example.FSDirectory: boolean isReservedName(example.INode)>";

    @Test
    public void refusesStaticConstantReadsAndKeepsStaticPrimitivesSelected()
            throws Exception {
        soot.G.reset();
        try {
            SootClass owner = new SootClass("example.FSDirectory",
                    Modifier.PUBLIC);
            Scene.v().addClass(owner);
            owner.setApplicationClass();
            SootField dotReserved = new SootField("DOT_RESERVED",
                    ArrayType.v(ByteType.v(), 1),
                    Modifier.PUBLIC | Modifier.STATIC | Modifier.FINAL);
            SootField checkNames = new SootField("CHECK_RESERVED_FILE_NAMES",
                    BooleanType.v(),
                    Modifier.PUBLIC | Modifier.STATIC | Modifier.FINAL);
            SootField mutableEpoch = new SootField("mutableEpoch",
                    IntType.v(), Modifier.PUBLIC | Modifier.STATIC);
            SootField mutableBytes = new SootField("mutableBytes",
                    ArrayType.v(ByteType.v(), 1),
                    Modifier.PUBLIC | Modifier.STATIC);
            SootField unselected = new SootField("unselected",
                    ArrayType.v(ByteType.v(), 1),
                    Modifier.PUBLIC | Modifier.STATIC);
            owner.addField(dotReserved);
            owner.addField(checkNames);
            owner.addField(mutableEpoch);
            owner.addField(mutableBytes);
            owner.addField(unselected);

            ConcolicInstrumentationSelections.ConcolicMaterializationSelection
                    selection = new ConcolicInstrumentationSelections
                    .ConcolicMaterializationSelection();
            selection.add(symbolicFieldRead(dotReserved.getSignature(),
                    "byte[]", ACTION_READER + "#u4"));
            selection.add(symbolicFieldRead(checkNames.getSignature(),
                    "boolean", ACTION_READER + "#u1"));
            selection.add(symbolicFieldRead(mutableEpoch.getSignature(),
                    "int", ACTION_READER + "#u2"));
            selection.add(symbolicFieldRead(mutableBytes.getSignature(),
                    "byte[]", ACTION_READER + "#u3"));

            // The crash: a site in another method that merely names the field.
            assertFalse(selection.matches(FATAL_READER, 25,
                    dotReserved.makeRef()));
            // Nor at the action's own read site: no getstatic has a receiver
            // for MATERIALIZE_FIELD and byte[] has no primitive round trip.
            assertFalse(selection.matches(ACTION_READER, 4,
                    dotReserved.makeRef()));
            assertFalse(selection.matches(ACTION_READER, 3,
                    mutableBytes.makeRef()));

            // Static primitives keep the static materializer they always had.
            assertTrue(selection.matches(ACTION_READER, 1,
                    checkNames.makeRef()));
            assertTrue(selection.matches(ACTION_READER, 2,
                    mutableEpoch.makeRef()));

            // A refusal is a verdict, and final and non-final are not the
            // same verdict: only the non-final one is a coverage gap.
            assertEquals(ConcolicInstrumentationSelections
                            .ConcolicMaterializationSelection.STATIC_CONSTANT,
                    selection.staticMaterializationRefusal(FATAL_READER, 25,
                            dotReserved.makeRef()));
            assertEquals(ConcolicInstrumentationSelections
                            .ConcolicMaterializationSelection
                            .STATIC_FIELD_UNSUPPORTED,
                    selection.staticMaterializationRefusal(ACTION_READER, 3,
                            mutableBytes.makeRef()));
            // Nothing to refuse where the plan selected nothing, or where the
            // static read is one the pipeline can materialize.
            assertEquals("", selection.staticMaterializationRefusal(
                    FATAL_READER, 9, unselected.makeRef()));
            assertEquals("", selection.staticMaterializationRefusal(
                    ACTION_READER, 1, checkNames.makeRef()));
        } finally {
            soot.G.reset();
        }
    }

    /** A static carrier read stays refused when only the carrier names it. */
    @Test
    public void refusesStaticCarrierWithoutASelectingAction() throws Exception {
        soot.G.reset();
        try {
            SootClass owner = new SootClass("example.CarrierOnly",
                    Modifier.PUBLIC);
            Scene.v().addClass(owner);
            owner.setApplicationClass();
            SootField bytes = new SootField("BYTES",
                    ArrayType.v(ByteType.v(), 1),
                    Modifier.PUBLIC | Modifier.STATIC | Modifier.FINAL);
            owner.addField(bytes);

            JsonObject carrier = new JsonObject();
            carrier.addProperty("kind", "DECLARED_FIELD");
            carrier.addProperty("declaringClass", owner.getName());
            carrier.addProperty("fieldName", "BYTES");
            carrier.addProperty("descriptor", "[B");
            carrier.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
            carrier.add("fieldPath", new JsonArray());
            JsonArray carriers = new JsonArray();
            carriers.add(carrier);

            ConcolicInstrumentationSelections.ConcolicMaterializationSelection
                    selection = new ConcolicInstrumentationSelections
                    .ConcolicMaterializationSelection();
            selection.addSharedCarrierTargets(carriers, new JsonArray());

            assertFalse(selection.matches(FATAL_READER, 25, bytes.makeRef()));
            assertEquals(ConcolicInstrumentationSelections
                            .ConcolicMaterializationSelection.STATIC_CONSTANT,
                    selection.staticMaterializationRefusal(FATAL_READER, 25,
                            bytes.makeRef()));
        } finally {
            soot.G.reset();
        }
    }

    private static JsonObject symbolicFieldRead(
            String fieldSignature, String javaType, String site) {
        JsonObject action = new JsonObject();
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("mintEligible", false);
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("sourceKind", "ACTIVATION_FIELD_RECEIVER");
        action.addProperty("accessFieldSignature", fieldSignature);
        action.addProperty("leafFieldSignature", fieldSignature);
        action.addProperty("javaType", javaType);
        action.addProperty("staticAccessSiteId", site);
        action.addProperty("siteId", site);
        return action;
    }
}
