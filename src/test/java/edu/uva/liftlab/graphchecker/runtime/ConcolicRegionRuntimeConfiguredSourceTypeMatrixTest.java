package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import org.junit.Test;

import java.lang.reflect.Field;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/** Model write-back coverage for exact manually declared source fields. */
public class ConcolicRegionRuntimeConfiguredSourceTypeMatrixTest {

    @Test
    public void tenPrimitiveSourceTypeChangesMaterializeWithoutTypeAssumptions()
            throws Exception {
        PrimitiveSources owner = new PrimitiveSources();
        SourceModel[] models = new SourceModel[] {
                model("enabled", "boolean", "BOOL", "true", true),
                model("disabled", "boolean", "BOOL", "false", false),
                model("tiny", "byte", "INT", "-7", (byte) -7),
                model("small", "short", "INT", "32000", (short) 32000),
                model("marker", "char", "INT", "90", 'Z'),
                model("count", "int", "INT", "-123456", -123456),
                model("distance", "long", "INT", "5000000000",
                        5_000_000_000L),
                model("ratio", "float", "REAL", "(/ 3 2)", 1.5f),
                model("threshold", "double", "REAL", "-2.25", -2.25d),
                model("upper", "int", "INT", "2147483647",
                        Integer.MAX_VALUE)
        };
        assertEquals(10, models.length);

        for (SourceModel model : models) {
            JsonObject encoded = new JsonObject();
            encoded.addProperty("modelAssignmentKey", "MODEL." + model.field);
            encoded.addProperty("valueType", model.valueType);
            encoded.addProperty("value", model.value);
            ConcolicRegionRuntime.ModelAssignment assignment =
                    new ConcolicRegionRuntime.ModelAssignment(encoded);
            String signature = "<" + PrimitiveSources.class.getName()
                    + ": " + model.javaType + " " + model.field + ">";

            assertTrue("write source " + model.field + " as "
                            + model.javaType,
                    ConcolicRegionRuntime.writeModeledField(
                            owner, signature, assignment));
            Field field = PrimitiveSources.class.getDeclaredField(model.field);
            field.setAccessible(true);
            assertEquals("materialized source " + model.field,
                    model.expected, field.get(owner));
        }
    }

    private static SourceModel model(
            String field, String javaType, String valueType, String value,
            Object expected) {
        return new SourceModel(field, javaType, valueType, value, expected);
    }

    private static final class SourceModel {
        private final String field;
        private final String javaType;
        private final String valueType;
        private final String value;
        private final Object expected;

        private SourceModel(String field, String javaType, String valueType,
                            String value, Object expected) {
            this.field = field;
            this.javaType = javaType;
            this.valueType = valueType;
            this.value = value;
            this.expected = expected;
        }
    }

    private static final class PrimitiveSources {
        private boolean enabled;
        private boolean disabled = true;
        private byte tiny;
        private short small;
        private char marker;
        private int count;
        private long distance;
        private float ratio;
        private double threshold;
        private int upper;
    }
}
