package edu.uva.liftlab.graphchecker.concolic;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

public class SmtModelValueCodecTest {
    @Test
    public void preservesStructuredNegativeAndFlattensOnlyNumericAtom() {
        assertEquals("-7", SmtModelValueCodec.normalizeScalar("(- 7)"));
        assertEquals("(- (/ 5.0 2.0))",
                SmtModelValueCodec.normalizeScalar("(- (/ 5.0 2.0))"));
    }

    @Test
    public void convertsPositiveAndNegativeRationalModelsForReplay() {
        assertEquals("2.5", SmtModelValueCodec.realToJavaLiteral(
                "(/ 5.0 2.0)"));
        assertEquals("-2.5", SmtModelValueCodec.realToJavaLiteral(
                "(- (/ 5.0 2.0))"));
        assertEquals("-2.5", SmtModelValueCodec.realToJavaLiteral(
                "(/ (- 5.0) 2.0)"));
        assertNull(SmtModelValueCodec.realToJavaLiteral("(/ 1.0 0.0)"));
        assertNull(SmtModelValueCodec.realToJavaLiteral("(root-obj ...)"));
        assertEquals("-0.0", SmtModelValueCodec.realToJavaLiteral("-0.0"));
        assertEquals("NaN", SmtModelValueCodec.realToJavaLiteral("NaN"));
        assertEquals("Infinity", SmtModelValueCodec.realToJavaLiteral(
                "Infinity"));
        assertEquals("1.4E-45", SmtModelValueCodec.realToJavaLiteral(
                "1.4e-45"));
        assertEquals("1.7976931348623157E308",
                SmtModelValueCodec.realToJavaLiteral(
                        "1.7976931348623157e+308"));
        assertEquals("-0.0", SmtModelValueCodec.realToJavaLiteral(
                "-0.0e+00"));
    }

    @Test
    public void decodesSmtQuotedStrings() {
        assertEquals("a\"b", SmtModelValueCodec.decodeString("\"a\"\"b\""));
    }

    @Test
    public void decodesExactIeeeBitsIncludingSignedZeroAndNonFinite() {
        assertEquals("-0.0", SmtModelValueCodec
                .floatingPointBitsToJavaLiteral("#x80000000", "F"));
        assertEquals("1.5", SmtModelValueCodec
                .floatingPointBitsToJavaLiteral(
                        "#x3ff8000000000000", "D"));
        assertEquals("Infinity", SmtModelValueCodec
                .floatingPointBitsToJavaLiteral(
                        "#x7ff0000000000000", "D"));
        assertEquals("-Infinity", SmtModelValueCodec
                .floatingPointBitsToJavaLiteral(
                        "#xfff0000000000000", "D"));
        assertEquals("NaN", SmtModelValueCodec
                .floatingPointBitsToJavaLiteral(
                        "#x7ff8000000000000", "D"));
        assertNull(SmtModelValueCodec.floatingPointBitsToJavaLiteral(
                "#x00000000", "D"));
        assertEquals("-0.0", SmtModelValueCodec
                .floatingPointTermToJavaLiteral("(_ -zero 11 53)", "D"));
        assertEquals("NaN", SmtModelValueCodec
                .floatingPointTermToJavaLiteral("(_ NaN 8 24)", "F"));
        assertEquals("1.5", SmtModelValueCodec
                .floatingPointTermToJavaLiteral(
                        "(fp #b0 #b01111111111 #x8000000000000)", "D"));
        assertEquals("1.4E-45", SmtModelValueCodec
                .floatingPointBitsToJavaLiteral("#x00000001", "F"));
        assertEquals("4.9E-324", SmtModelValueCodec
                .floatingPointBitsToJavaLiteral(
                        "#x0000000000000001", "D"));
    }
}
