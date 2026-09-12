package edu.uva.liftlab.graphchecker.contract;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/** {@code <method>#u<unitIndex>}: one spelling of one bytecode site. */
public class SiteIdTest {
    private static final String METHOD =
            "<org.apache.hadoop.hdfs.server.namenode.FSNamesystem:"
                    + " void startFile()>";

    @Test
    public void aSiteIsItsMethodAndUnitIndex() {
        assertEquals(METHOD + "#u0", SiteId.of(METHOD, 0));
        assertEquals(METHOD + "#u137", SiteId.of(METHOD, 137));
    }

    @Test
    public void aRenderedSiteReadsItsUnitIndexBack() {
        assertEquals(0, SiteId.unitIndexOf(SiteId.of(METHOD, 0)));
        assertEquals(137, SiteId.unitIndexOf(SiteId.of(METHOD, 137)));
    }

    @Test
    public void aStringThatNamesNoUnitHasNoUnitIndex() {
        for (String written : new String[] {
                null, "", METHOD, METHOD + "#u", METHOD + "#ux",
                METHOD + "#u1x"}) {
            assertEquals(String.valueOf(written), -1,
                    SiteId.unitIndexOf(written));
        }
    }

    @Test
    public void aRenderedKeyKeepsTheNoUnitSentinel() {
        assertEquals(METHOD + "#u-1", SiteId.render(METHOD, -1));
        assertEquals(METHOD + "#u0", SiteId.render(METHOD, 0));
        assertEquals(METHOD + "#u137", SiteId.render(METHOD, 137));
        for (String method : new String[] {null, "", "   "}) {
            try {
                SiteId.render(method, -1);
                fail("expected a refusal for method " + method);
            } catch (IllegalArgumentException expected) {
                assertEquals("method is required", expected.getMessage());
            }
        }
    }

    @Test
    public void aBlankMethodOrNegativeUnitIsNotASite() {
        for (String method : new String[] {null, "", "   "}) {
            try {
                SiteId.of(method, 3);
                fail("expected a refusal for method " + method);
            } catch (IllegalArgumentException expected) {
                assertEquals("method is required", expected.getMessage());
            }
        }
        try {
            SiteId.of(METHOD, -1);
            fail("expected a refusal for a negative unit index");
        } catch (IllegalArgumentException expected) {
            assertEquals("unitIndex must be non-negative",
                    expected.getMessage());
        }
    }
}
